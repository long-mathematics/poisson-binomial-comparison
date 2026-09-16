import PoissonBinomialComparison.HomogeneousDerivative
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Elementary geometry of homogeneous switches

Rolle's theorem locates the unique critical point of the equal-height polynomial
strictly between the switch parameters. The remaining identities are algebraic.
-/

namespace PoissonBinomialComparison

private theorem hasDerivAt_switchHeight {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    (x : ℝ) :
    HasDerivAt (fun u : ℝ ↦ u ^ j * (1 - u) ^ (n - j))
      (x ^ (j - 1) * (1 - x) ^ (n - j - 1) * ((j : ℝ) - n * x)) x := by
  have hd := ((hasDerivAt_id x).pow j).mul
    (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow (n - j))
  convert hd using 1
  · funext u
    rfl
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
  have hjpow : x ^ j = x ^ (j - 1) * x := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  have hnjpow : (1 - x) ^ (n - j) = (1 - x) ^ (n - j - 1) * (1 - x) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n - j)]
  rw [hjpow, hnjpow, Nat.cast_sub hjn.le]
  ring

/-- The switching count divided by dimension lies strictly between the parameters. -/
theorem IsSwitch.center_bounds {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b)
    (hj : 0 < j) (hjn : j < n) : b < (j : ℝ) / n ∧ (j : ℝ) / n < a := by
  obtain ⟨x, hx, hderiv⟩ := exists_hasDerivAt_eq_zero h.2.1
    (by fun_prop : ContinuousOn (fun u : ℝ ↦ u ^ j * (1 - u) ^ (n - j)) (Set.Icc b a))
    h.2.2.2.2.symm (fun x _ ↦ hasDerivAt_switchHeight hj hjn x)
  have hx0 : 0 < x := lt_trans h.1 hx.1
  have hx1 : 0 < 1 - x := by linarith [h.2.2.1, hx.2]
  have hfac : 0 < x ^ (j - 1) * (1 - x) ^ (n - j - 1) :=
    mul_pos (pow_pos hx0 _) (pow_pos hx1 _)
  have hz : (j : ℝ) - n * x = 0 := (mul_eq_zero.mp hderiv).resolve_left hfac.ne'
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hxc : x = (j : ℝ) / n := (eq_div_iff hn).2 (by linarith)
  exact hxc ▸ hx

/-- Complementing both laws reflects the switching count. -/
theorem IsSwitch.reflect {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b)
    (hj : j ≤ n) : IsSwitch n (n - j) γ (1 - b) (1 - a) := by
  refine ⟨by linarith [h.2.2.1], by linarith [h.2.1], by linarith [h.1],
    by linarith [h.2.2.2.1], ?_⟩
  simpa only [sub_sub_cancel, Nat.sub_sub_self hj, mul_comm] using h.2.2.2.2.symm

/-- The denominator identity before division by `c(1-c)`. -/
theorem switch_denominator_identity (c a b : ℝ) :
    c * (1 - c) - (a - c) * (c - b) =
      c * (1 - a) * (1 - b) + (1 - c) * a * b := by
  ring

/-- The switch denominator is strictly positive at its central count ratio. -/
theorem IsSwitch.denominator_pos {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b)
    (hj : 0 < j) (hjn : j < n) :
    0 < ((j : ℝ) / n) * (1 - a) * (1 - b) + (1 - (j : ℝ) / n) * a * b := by
  obtain ⟨hbc, hca⟩ := h.center_bounds hj hjn
  have hc0 : 0 < (j : ℝ) / n := lt_trans h.1 hbc
  have hc1 : 0 < 1 - (j : ℝ) / n := by linarith [h.2.2.1]
  have ha0 : 0 < a := lt_trans h.1 h.2.1
  have ha1 : 0 < 1 - a := by linarith [h.2.2.1]
  have hb1 : 0 < 1 - b := by linarith [h.2.1, h.2.2.1]
  exact add_pos (mul_pos (mul_pos hc0 ha1) hb1) (mul_pos (mul_pos hc1 ha0) h.1)

/-- The geometric ratio `R` of the manuscript is strictly between zero and one. -/
theorem IsSwitch.geometric_ratio_bounds {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (hj : 0 < j) (hjn : j < n) :
    let c := (j : ℝ) / n
    0 < (a - c) * (c - b) / (c * (1 - c)) ∧
      (a - c) * (c - b) / (c * (1 - c)) < 1 := by
  dsimp
  obtain ⟨hbc, hca⟩ := h.center_bounds hj hjn
  have hc0 : 0 < (j : ℝ) / n := lt_trans h.1 hbc
  have hc1 : 0 < 1 - (j : ℝ) / n := by linarith [h.2.2.1]
  have hv : 0 < ((j : ℝ) / n) * (1 - (j : ℝ) / n) := mul_pos hc0 hc1
  refine ⟨div_pos (mul_pos (sub_pos.mpr hca) (sub_pos.mpr hbc)) hv, ?_⟩
  apply (div_lt_one hv).2
  have hid := switch_denominator_identity ((j : ℝ) / n) a b
  have hp := h.denominator_pos hj hjn
  linarith

/-- The normalized denominator identity `v(1-R)` used in switch differentiation. -/
theorem IsSwitch.normalized_denominator {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (hj : 0 < j) (hjn : j < n) :
    let c := (j : ℝ) / n
    c * (1 - c) * (1 - (a - c) * (c - b) / (c * (1 - c))) =
      c * (1 - a) * (1 - b) + (1 - c) * a * b := by
  dsimp
  obtain ⟨hbc, hca⟩ := h.center_bounds hj hjn
  have hc0 : 0 < (j : ℝ) / n := lt_trans h.1 hbc
  have hc1 : 0 < 1 - (j : ℝ) / n := by linarith [h.2.2.1]
  have hv : ((j : ℝ) / n) * (1 - (j : ℝ) / n) ≠ 0 := (mul_pos hc0 hc1).ne'
  rw [mul_sub, mul_one, mul_div_cancel₀ _ hv]
  exact switch_denominator_identity ((j : ℝ) / n) a b

/-- The common coordinate adjoined in the strict dimension-improvement argument. -/
noncomputable def switchRho (n j : ℕ) (a b : ℝ) : ℝ :=
  (n - j : ℕ) * a * b / ((n - j : ℕ) * a * b + (j : ℝ) * (1 - a) * (1 - b))

/-- The adjoined common coordinate is a strictly interior Bernoulli parameter. -/
theorem IsSwitch.switchRho_mem_Ioo {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (hj : 0 < j) (hjn : j < n) :
    switchRho n j a b ∈ Set.Ioo (0 : ℝ) 1 := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hnj' : (0 : ℝ) < (n - j : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hjn)
  have ha0 : 0 < a := lt_trans h.1 h.2.1
  have ha1 : 0 < 1 - a := by linarith [h.2.2.1]
  have hb1 : 0 < 1 - b := by linarith [h.2.1, h.2.2.1]
  have hp : 0 < (n - j : ℕ) * a * b := mul_pos (mul_pos hnj' ha0) h.1
  have hq : 0 < (j : ℝ) * (1 - a) * (1 - b) := mul_pos (mul_pos hj' ha1) hb1
  exact ⟨div_pos hp (add_pos hp hq), (div_lt_one (add_pos hp hq)).2 (by linarith)⟩

end PoissonBinomialComparison
