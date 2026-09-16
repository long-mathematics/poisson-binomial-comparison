import PoissonBinomialComparison.BenchmarkConcavity
import PoissonBinomialComparison.HomogeneousMinimum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Explicit integral formulas for the benchmark -/

namespace PoissonBinomialComparison

open MeasureTheory Set

noncomputable section

/-- Algebraic binomial tails satisfy the usual integrated density formula. -/
theorem tailDiff_const_eq_integral (n k : ℕ) (a b : ℝ) :
    tailDiff (fun _ : Fin n ↦ a) (fun _ ↦ b) (k + 1) =
      n * (∫ u in b..a, pbMass (fun _ : Fin (n - 1) ↦ u) k) := by
  have hd := fun u ↦ hasDerivAt_pbTail_const_succ n k u
  have hc : Continuous (fun u : ℝ ↦ pbMass (fun _ : Fin (n - 1) ↦ u) k) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ (hd u)) ((hc.const_mul (n : ℝ)).intervalIntegrable b a)
  rw [intervalIntegral.integral_const_mul] at hi
  exact hi.symm

/-- The odd-dimensional integral formula at any interior switch. -/
theorem IsSwitch.odd_integral {m : ℕ} {γ a b : ℝ}
    (h : IsSwitch (2 * m + 1) m γ a b) (hm : 0 < m) :
    tailObjective (fun _ : Fin (2 * m + 1) ↦ a) (fun _ ↦ b) =
      (2 * m + 1 : ℝ) * ((2 * m).choose m : ℝ) *
        (∫ u in b..a, (u * (1 - u)) ^ m) := by
  have heq := tailDiff_sub_succ (fun _ : Fin (2 * m + 1) ↦ a) (fun _ ↦ b) m
  rw [h.pbMass_eq, sub_self] at heq
  rw [h.tailObjective_eq hm (by omega), sub_eq_zero.mp heq,
    tailDiff_const_eq_integral]
  have hf : (fun u : ℝ ↦ pbMass (fun _ : Fin (2 * m + 1 - 1) ↦ u) m) =
      (fun u ↦ ((2 * m).choose m : ℝ) * (u * (1 - u)) ^ m) := by
    funext u
    simp only [show 2 * m + 1 - 1 = 2 * m by omega, pbMass_const,
      show 2 * m - m = m by omega, mul_pow]
    ring
  rw [hf, intervalIntegral.integral_const_mul]
  push_cast
  ring

/-- Equation `odd-integral` in terms of the canonical switch parameters. -/
theorem benchmark_odd_integral {m : ℕ} (hm : 0 < m) {Δ : ℝ}
    (hΔ0 : 0 < Δ) (hΔn : Δ < 2 * m + 1) :
    benchmark (2 * m + 1) Δ =
      (2 * m + 1 : ℝ) * ((2 * m).choose m : ℝ) *
        (∫ u in switchLower (2 * m + 1) m (Δ / (2 * m + 1))..
          switchUpper (2 * m + 1) m (Δ / (2 * m + 1)), (u * (1 - u)) ^ m) := by
  have hn0 : (0 : ℝ) < 2 * m + 1 := by positivity
  have hγ0 : 0 < Δ / (2 * m + 1) := div_pos hΔ0 hn0
  have hγ1 : Δ / (2 * m + 1) < 1 := (div_lt_one hn0).mpr hΔn
  have hs := switchPair_spec (n := 2 * m + 1) hm (by omega) hγ0 hγ1
  rw [benchmark_eq_switchValue hΔ0 (by exact_mod_cast hΔn)]
  simp only [show (2 * m + 1) / 2 = m by omega]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    (hs.tailObjective_eq_switchValue hm (by omega)).symm.trans (hs.odd_integral hm)

private theorem central_choose_twice {m : ℕ} (hm : 0 < m) :
    (2 * m).choose m = 2 * (2 * m - 1).choose (m - 1) := by
  have hr := Nat.choose_succ_succ' (2 * m - 1) (m - 1)
  have hs := Nat.choose_symm (show m ≤ 2 * m - 1 by omega)
  rw [show 2 * m - 1 - m = m - 1 by omega] at hs
  rw [show 2 * m - 1 + 1 = 2 * m by omega,
    show m - 1 + 1 = m by omega, ← hs] at hr
  omega

/-- The complementary deleted-coordinate masses combine into the even density. -/
theorem complementary_mass_density {m : ℕ} (hm : 0 < m) (t : ℝ) :
    (pbMass (fun _ : Fin (2 * m - 1) ↦ (1 + t) / 2) (m - 1) +
      pbMass (fun _ : Fin (2 * m - 1) ↦ (1 - t) / 2) (m - 1)) / 2 =
      ((2 * m).choose m : ℝ) / (2 : ℝ) ^ (2 * m) * (1 - t ^ 2) ^ (m - 1) := by
  have hc : ((2 * m).choose m : ℝ) = 2 * ((2 * m - 1).choose (m - 1) : ℝ) := by
    exact_mod_cast central_choose_twice hm
  rw [hc]
  simp only [pbMass_const, show 2 * m - 1 - (m - 1) = m by omega]
  have hpa : 1 - (1 + t) / 2 = (1 - t) / 2 := by ring
  have hpb : 1 - (1 - t) / 2 = (1 + t) / 2 := by ring
  rw [hpa, hpb]
  have hsum : ((1 + t) / 2) ^ (m - 1) * ((1 - t) / 2) ^ m +
      ((1 - t) / 2) ^ (m - 1) * ((1 + t) / 2) ^ m =
      ((1 - t ^ 2) / 4) ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    conv_lhs => simp only [Nat.add_sub_cancel, pow_succ]
    rw [show (1 - t ^ 2) / 4 = ((1 + t) / 2) * ((1 - t) / 2) by ring, mul_pow]
    ring
  have hpow : (2 : ℝ) ^ (2 * m) = 4 * 4 ^ (m - 1) := by
    rw [pow_mul, show m = (m - 1) + 1 by omega, pow_succ]
    norm_num
    ring
  conv_rhs at hsum => rw [div_pow]
  rw [hpow]
  linear_combination ((2 * m - 1).choose (m - 1) : ℝ) / 2 * hsum

/-- The complementary central-tail representation includes both endpoints. -/
theorem switchValue_even_closed {m : ℕ} (hm : 0 < m) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    switchValue (2 * m) m γ =
      tailDiff (fun _ : Fin (2 * m) ↦ (1 + γ) / 2) (fun _ ↦ (1 - γ) / 2) m := by
  by_cases h0 : γ = 0
  · subst γ
    simp [tailDiff]
  by_cases h1 : γ = 1
  · subst γ
    simp only [switchValue_one (n := 2 * m) hm (by omega), add_self_div_two, sub_self, zero_div]
    simp [tailDiff, pbTail_const_one, pbTail_const_zero, hm.ne', show m ≤ 2 * m by omega]
  · obtain ⟨ha, hb⟩ := switchPair_even hm (lt_of_le_of_ne hγ0 (Ne.symm h0))
      (lt_of_le_of_ne hγ1 h1)
    exact congrArg₂ (fun a b : ℝ ↦ tailDiff (fun _ : Fin (2 * m) ↦ a) (fun _ ↦ b) m) ha hb

/-- The derivative in total-gap coordinates gives the even integrand. -/
theorem hasDerivAt_even_tail {m : ℕ} (hm : 0 < m) (u : ℝ) :
    HasDerivAt
      (fun x : ℝ ↦ tailDiff (fun _ : Fin (2 * m) ↦ (1 + x / (2 * m)) / 2)
        (fun _ ↦ (1 - x / (2 * m)) / 2) m)
      (((2 * m).choose m : ℝ) / (2 : ℝ) ^ (2 * m) *
        (1 - u ^ 2 / (2 * m : ℝ) ^ 2) ^ (m - 1)) u := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hA : HasDerivAt (fun x : ℝ ↦ (1 + x / (2 * m)) / 2) (1 / (4 * m)) u := by
    convert (((hasDerivAt_id u).div_const (2 * (m : ℝ))).const_add 1).div_const 2 using 1 <;>
      first | rfl | ring
  have hB : HasDerivAt (fun x : ℝ ↦ (1 - x / (2 * m)) / 2) (-1 / (4 * m)) u := by
    convert (((hasDerivAt_id u).div_const (2 * (m : ℝ))).const_sub 1).div_const 2 using 1 <;>
      first | rfl | ring
  have hp := (hasDerivAt_pbTail_const (2 * m) m hm ((1 + u / (2 * m)) / 2)).comp u hA
  have hq := (hasDerivAt_pbTail_const (2 * m) m hm ((1 - u / (2 * m)) / 2)).comp u hB
  convert hp.sub hq using 1
  · rfl
  · have hh := complementary_mass_density hm (u / (2 * m))
    simp only [div_pow] at hh
    rw [← hh]
    push_cast
    field_simp
    ring

/-- The manuscript's even-dimensional benchmark integral, for the entire
closed total-gap interval. The coefficient `2⁻ⁿ` is written as division by `2^n`. -/
theorem benchmark_even_integral {m : ℕ} (hm : 0 < m) {Δ : ℝ}
    (hΔ0 : 0 ≤ Δ) (hΔn : Δ ≤ 2 * m) :
    benchmark (2 * m) Δ =
      ((2 * m).choose m : ℝ) / (2 : ℝ) ^ (2 * m) *
        (∫ u in (0 : ℝ)..Δ, (1 - u ^ 2 / (2 * m : ℝ) ^ 2) ^ (m - 1)) := by
  have hm0 : (0 : ℝ) < 2 * m := by positivity
  have hγ0 : 0 ≤ Δ / (2 * m) := div_nonneg hΔ0 hm0.le
  have hγ1 : Δ / (2 * m) ≤ 1 := (div_le_one hm0).mpr hΔn
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ hasDerivAt_even_tail hm u)
    (show IntervalIntegrable
      (fun u : ℝ ↦ ((2 * m).choose m : ℝ) / (2 : ℝ) ^ (2 * m) *
        (1 - u ^ 2 / (2 * m : ℝ) ^ 2) ^ (m - 1)) volume 0 Δ from
      (by fun_prop : Continuous _).intervalIntegrable 0 Δ)
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [zero_div, add_zero, sub_zero, tailDiff, sub_self] at hi
  rw [benchmark_eq_switchValue_of_mem (by omega) ⟨hΔ0, by exact_mod_cast hΔn⟩]
  simp only [show 2 * m / 2 = m by omega, Nat.cast_mul, Nat.cast_ofNat]
  rw [switchValue_even_closed hm hγ0 hγ1]
  exact hi.symm

private theorem pbTail_three_two (a : ℝ) :
    pbTail (fun _ : Fin 3 ↦ a) 2 = 3 * a ^ 2 - 2 * a ^ 3 := by
  norm_num [pbTail_const, Finset.sum_Icc_succ_top]
  ring

/-- The explicit radical for the three-dimensional switch value. -/
theorem IsSwitch.three_radical {γ a b : ℝ} (h : IsSwitch 3 1 γ a b) :
    tailObjective (fun _ : Fin 3 ↦ a) (fun _ ↦ b) =
      (2 * γ / 3) * (1 + Real.sqrt (1 - 3 * γ ^ 2 / 4)) := by
  have hγ : 0 < γ := by linarith [h.2.1, h.2.2.2.1]
  have hγ1 : γ < 1 := by linarith [h.1, h.2.2.1, h.2.2.2.1]
  have heq := h.2.2.2.2
  norm_num at heq
  have hfactor : (a - b) * (a ^ 2 + a * b + b ^ 2 - 2 * (a + b) + 1) = 0 := by
    nlinarith [heq]
  have hpoly : a ^ 2 + a * b + b ^ 2 - 2 * (a + b) + 1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_pos.mpr h.2.1).ne'
  have hcenter := h.center_bounds (by norm_num) (by norm_num)
  have hspos : 0 ≤ (4 - 3 * (a + b)) / 2 := by
    norm_num at hcenter
    linarith [h.2.2.1]
  have hsquare : ((4 - 3 * (a + b)) / 2) ^ 2 = 1 - 3 * γ ^ 2 / 4 := by
    rw [← h.2.2.2.1]
    nlinarith [hpoly]
  have hsqrt : Real.sqrt (1 - 3 * γ ^ 2 / 4) = (4 - 3 * (a + b)) / 2 := by
    rw [← hsquare, Real.sqrt_sq hspos]
  have htail := tailDiff_sub_succ (fun _ : Fin 3 ↦ a) (fun _ ↦ b) 1
  rw [h.pbMass_eq, sub_self] at htail
  rw [h.tailObjective_eq (by norm_num) (by norm_num), sub_eq_zero.mp htail]
  norm_num only at ⊢
  rw [tailDiff, pbTail_three_two, pbTail_three_two, hsqrt, ← h.2.2.2.1]
  linear_combination -2 * (a - b) * hpoly

/-- The manuscript's closed radical formula for `B₃`, including both endpoints. -/
theorem benchmark_three_radical {Δ : ℝ} (hΔ0 : 0 ≤ Δ) (hΔ3 : Δ ≤ 3) :
    benchmark 3 Δ = (2 * Δ / 9) * (1 + Real.sqrt (1 - Δ ^ 2 / 12)) := by
  by_cases h0 : Δ = 0
  · simp [h0]
  by_cases h3 : Δ = 3
  · subst Δ
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
      convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1
      norm_num
    norm_num [benchmark, hsqrt4]
  have hpos : 0 < Δ := lt_of_le_of_ne hΔ0 (Ne.symm h0)
  have hlt : Δ < 3 := lt_of_le_of_ne hΔ3 h3
  have hs := switchPair_spec (n := 3) (j := 1) (by norm_num) (by norm_num)
    (show 0 < Δ / 3 by positivity) (show Δ / 3 < 1 by linarith)
  rw [benchmark_eq_switchValue hpos (by exact_mod_cast hlt)]
  norm_num only
  rw [← hs.tailObjective_eq_switchValue (by norm_num) (by norm_num), hs.three_radical]
  rw [show 1 - 3 * (Δ / 3) ^ 2 / 4 = 1 - Δ ^ 2 / 12 by ring]
  ring

/-- The odd central tail itself has the symmetric polynomial density. -/
theorem tailDiff_odd_integral (m : ℕ) (a b : ℝ) :
    tailDiff (fun _ : Fin (2 * m + 1) ↦ a) (fun _ ↦ b) (m + 1) =
      (2 * m + 1 : ℝ) * ((2 * m).choose m : ℝ) *
        (∫ u in b..a, (u * (1 - u)) ^ m) := by
  rw [tailDiff_const_eq_integral]
  have hf : (fun u : ℝ ↦ pbMass (fun _ : Fin (2 * m + 1 - 1) ↦ u) m) =
      (fun u ↦ ((2 * m).choose m : ℝ) * (u * (1 - u)) ^ m) := by
    funext u
    simp only [show 2 * m + 1 - 1 = 2 * m by omega, pbMass_const,
      show 2 * m - m = m by omega, mul_pow]
    ring
  rw [hf, intervalIntegral.integral_const_mul]
  push_cast
  ring

/-- The odd integral with the canonical endpoint conventions is valid on the
entire closed total-gap interval. -/
theorem benchmark_odd_integral_closed {m : ℕ} (hm : 0 < m) {Δ : ℝ}
    (hΔ0 : 0 ≤ Δ) (hΔn : Δ ≤ 2 * m + 1) :
    benchmark (2 * m + 1) Δ =
      (2 * m + 1 : ℝ) * ((2 * m).choose m : ℝ) *
        (∫ u in switchLower (2 * m + 1) m (Δ / (2 * m + 1))..
          switchUpper (2 * m + 1) m (Δ / (2 * m + 1)), (u * (1 - u)) ^ m) := by
  by_cases h0 : Δ = 0
  · simp [h0]
  by_cases hn : Δ = 2 * m + 1
  · have hdim : Δ = ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    rw [hdim, benchmark_at_dimension (by omega)]
    have hne : (2 * m + 1 : ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, div_self hne,
      switchUpper_one, switchLower_one]
    have hi := tailDiff_odd_integral m 1 0
    simpa [tailDiff, pbTail_const_one, pbTail_const_zero, show m + 1 ≤ 2 * m + 1 by omega] using hi
  · exact benchmark_odd_integral hm (lt_of_le_of_ne hΔ0 (Ne.symm h0))
      (lt_of_le_of_ne hΔn hn)

end

end PoissonBinomialComparison
