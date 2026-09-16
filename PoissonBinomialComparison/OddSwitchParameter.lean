import PoissonBinomialComparison.BenchmarkExplicit

/-! # The odd-dimensional rational switch parameter -/

namespace PoissonBinomialComparison

noncomputable section

/-- The rational gap function in the manuscript's odd parameterization. -/
def oddSwitchGap (m : ℕ) (z : ℝ) : ℝ :=
  ((z ^ m - 1) * (z ^ (m + 1) - 1)) / (z ^ (2 * m + 1) - 1)

/-- The lower Bernoulli parameter of an odd switch. -/
def oddSwitchLower (m : ℕ) (z : ℝ) : ℝ :=
  (z ^ m - 1) / (z ^ (2 * m + 1) - 1)

/-- The upper Bernoulli parameter of an odd switch. -/
def oddSwitchUpper (m : ℕ) (z : ℝ) : ℝ :=
  z ^ (m + 1) * (z ^ m - 1) / (z ^ (2 * m + 1) - 1)

/-- Every `z > 1` gives precisely an interior odd switch. -/
theorem isSwitch_odd_parameter {m : ℕ} (hm : 0 < m) {z : ℝ} (hz : 1 < z) :
    IsSwitch (2 * m + 1) m (oddSwitchGap m z) (oddSwitchUpper m z) (oddSwitchLower m z) := by
  have hx : 1 < z ^ m := one_lt_pow₀ hz hm.ne'
  have hy : 1 < z ^ (m + 1) := one_lt_pow₀ hz (by omega)
  have hpow : z ^ (2 * m + 1) = z ^ m * z ^ (m + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hd : 0 < z ^ (2 * m + 1) - 1 := by rw [hpow]; nlinarith
  have hb : 0 < oddSwitchLower m z := div_pos (sub_pos.mpr hx) hd
  have hab : oddSwitchUpper m z = z ^ (m + 1) * oddSwitchLower m z := by
    simp only [oddSwitchUpper, oddSwitchLower]
    ring
  have hca : 1 - oddSwitchUpper m z = (z ^ (m + 1) - 1) / (z ^ (2 * m + 1) - 1) := by
    dsimp [oddSwitchUpper]
    field_simp
    rw [hpow]
    ring
  have hcb : 1 - oddSwitchLower m z = z ^ m * (1 - oddSwitchUpper m z) := by
    rw [hca]
    dsimp [oddSwitchLower]
    field_simp
    rw [hpow]
    ring
  refine ⟨hb, ?_, ?_, ?_, ?_⟩
  · rw [hab]
    nlinarith
  · have hp := div_pos (sub_pos.mpr hy) hd
    rw [← hca] at hp
    linarith
  · dsimp [oddSwitchUpper, oddSwitchLower, oddSwitchGap]
    ring
  · rw [show 2 * m + 1 - m = m + 1 by omega, hcb, hab, mul_pow, mul_pow]
    have hp : (z ^ (m + 1)) ^ m = (z ^ m) ^ (m + 1) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hp]
    ring

/-- The rational parameter is recovered intrinsically from its Bernoulli pair. -/
theorem odd_parameter_recover {m : ℕ} (hm : 0 < m) {z : ℝ} (hz : 1 < z) :
    oddSwitchUpper m z * (1 - oddSwitchUpper m z) /
      (oddSwitchLower m z * (1 - oddSwitchLower m z)) = z := by
  have hs := isSwitch_odd_parameter hm hz
  have hx : z ^ m ≠ 1 := ne_of_gt (one_lt_pow₀ hz hm.ne')
  have hy : z ^ (m + 1) ≠ 1 := ne_of_gt (one_lt_pow₀ hz (by omega))
  have hd : z ^ (2 * m + 1) - 1 ≠ 0 :=
    (sub_pos.mpr (one_lt_pow₀ hz (by omega))).ne'
  have hz0 : z ≠ 0 := by linarith
  have hpow : z ^ (2 * m + 1) = z ^ m * z ^ (m + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hab : oddSwitchUpper m z = z ^ (m + 1) * oddSwitchLower m z := by
    simp only [oddSwitchUpper, oddSwitchLower]
    ring
  have hcb : 1 - oddSwitchLower m z = z ^ m * (1 - oddSwitchUpper m z) := by
    dsimp [oddSwitchUpper, oddSwitchLower]
    field_simp
    rw [hpow]
    ring
  have hb0 := hs.1.ne'
  have hca0 := (sub_pos.mpr hs.2.2.1).ne'
  rw [hcb]
  nth_rw 1 [hab]
  field_simp
  rw [pow_succ]

/-- Every interior odd switch has the manuscript's rational parameterization. -/
theorem IsSwitch.exists_odd_parameter {m : ℕ} (hm : 0 < m) {γ a b : ℝ}
    (h : IsSwitch (2 * m + 1) m γ a b) :
    ∃ z : ℝ, 1 < z ∧ a = oddSwitchUpper m z ∧ b = oddSwitchLower m z ∧
      oddSwitchGap m z = γ := by
  let x := a / b
  let y := (1 - b) / (1 - a)
  have hb0 : b ≠ 0 := h.1.ne'
  have ha0 : 0 < 1 - a := sub_pos.mpr h.2.2.1
  have hy1 : 1 < y := (one_lt_div ha0).mpr (by linarith [h.2.1])
  have hy0 : y ≠ 0 := by linarith
  have hx0 : 0 < x := div_pos (h.1.trans h.2.1) h.1
  have hxy : x ^ m = y ^ (m + 1) := by
    dsimp [x, y]
    rw [div_pow, div_pow]
    apply (div_eq_div_iff (pow_ne_zero _ hb0) (pow_ne_zero _ ha0.ne')).mpr
    have heq := h.2.2.2.2
    rw [show 2 * m + 1 - m = m + 1 by omega] at heq
    nlinarith [heq]
  let z := x / y
  have hz0 : 0 < z := div_pos hx0 (by linarith)
  have hzm : z ^ m = y := by
    dsimp [z]
    rw [div_pow, hxy, pow_succ]
    field_simp
  have hzm1 : z ^ (m + 1) = x := by
    rw [pow_succ, hzm]
    dsimp [z]
    field_simp
  have hz1 : 1 < z := by
    by_contra hnot
    have hh := pow_le_one₀ (n := m) hz0.le (le_of_not_gt hnot)
    rw [hzm] at hh
    linarith
  have hd : z ^ (2 * m + 1) - 1 ≠ 0 :=
    (sub_pos.mpr (one_lt_pow₀ hz1 (by omega))).ne'
  have hp : z ^ (2 * m + 1) = z ^ m * z ^ (m + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hza : a = z ^ (m + 1) * b := by rw [hzm1]; dsimp [x]; field_simp
  have hzb : 1 - b = z ^ m * (1 - a) := by rw [hzm]; dsimp [y]; field_simp
  have hb : b = oddSwitchLower m z := by
    dsimp [oddSwitchLower]
    apply (eq_div_iff hd).mpr
    rw [hp]
    rw [hza] at hzb
    nlinarith [hzb]
  have ha : a = oddSwitchUpper m z := by
    rw [hza, hb]
    dsimp [oddSwitchUpper, oddSwitchLower]
    ring
  refine ⟨z, hz1, ha, hb, ?_⟩
  have hs := isSwitch_odd_parameter hm hz1
  rw [← ha, ← hb] at hs
  exact hs.2.2.2.1.symm.trans h.2.2.2.1

/-- There is exactly one `z > 1` solving the manuscript's odd gap equation. -/
theorem existsUnique_odd_parameter {m : ℕ} (hm : 0 < m) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃! z : ℝ, 1 < z ∧ oddSwitchGap m z = γ := by
  obtain ⟨a, b, hs⟩ := exists_switch (n := 2 * m + 1) hm (by omega) hγ0 hγ1
  obtain ⟨z, hz, ha, hb, hgap⟩ := hs.exists_odd_parameter hm
  refine ⟨z, ⟨hz, hgap⟩, ?_⟩
  intro w hw
  have hsw := isSwitch_odd_parameter hm hw.1
  have hsz := isSwitch_odd_parameter hm hz
  rw [hw.2] at hsw
  rw [hgap] at hsz
  obtain ⟨hu, hl⟩ := switch_unique hm (by omega) hγ0 hsw hsz
  have hr := odd_parameter_recover hm hw.1
  rw [hu, hl, odd_parameter_recover hm hz] at hr
  exact hr.symm

/-- The unique parameter gives exactly the selected canonical switch pair. -/
theorem odd_parameter_eq_switchPair {m : ℕ} (hm : 0 < m) {γ z : ℝ}
    (hz : 1 < z) (hgap : oddSwitchGap m z = γ) :
    switchUpper (2 * m + 1) m γ = oddSwitchUpper m z ∧
      switchLower (2 * m + 1) m γ = oddSwitchLower m z := by
  have hs := isSwitch_odd_parameter hm hz
  rw [hgap] at hs
  obtain ⟨ha, hb⟩ := hs.eq_switchPair hm (by omega)
  exact ⟨ha.symm, hb.symm⟩

/-- The unique-solution statement in the total-gap coordinates of the paper. -/
theorem existsUnique_odd_parameter_totalGap {m : ℕ} (hm : 0 < m) {Δ : ℝ}
    (hΔ0 : 0 < Δ) (hΔn : Δ < 2 * m + 1) :
    ∃! z : ℝ, 1 < z ∧
      ((z ^ m - 1) * (z ^ (m + 1) - 1)) / (z ^ (2 * m + 1) - 1) =
        Δ / (2 * m + 1) := by
  have hn : (0 : ℝ) < 2 * m + 1 := by positivity
  exact existsUnique_odd_parameter hm (div_pos hΔ0 hn) ((div_lt_one hn).mpr hΔn)

/-- Substituting the unique rational parameters into the exact odd integral
recovers the benchmark without reference to a global minimization theorem. -/
theorem benchmark_odd_integral_of_parameter {m : ℕ} (hm : 0 < m) {Δ z : ℝ}
    (hΔ0 : 0 < Δ) (hΔn : Δ < 2 * m + 1) (hz : 1 < z)
    (hgap : oddSwitchGap m z = Δ / (2 * m + 1)) :
    benchmark (2 * m + 1) Δ =
      (2 * m + 1 : ℝ) * ((2 * m).choose m : ℝ) *
        (∫ u in oddSwitchLower m z..oddSwitchUpper m z, (u * (1 - u)) ^ m) := by
  rw [benchmark_odd_integral hm hΔ0 hΔn]
  obtain ⟨ha, hb⟩ := odd_parameter_eq_switchPair hm hz hgap
  rw [ha, hb]

end

end PoissonBinomialComparison
