import PoissonBinomialComparison.SwitchDerivative
import PoissonBinomialComparison.Reindex

/-!
# The density of the common-coordinate dimension improvement

The manuscript's randomizing parameter `rho` makes the deleted-coordinate
binomial mixture have the same value at both switch parameters. That common
value is exactly `f / (1 - R)` and strictly exceeds the tied count mass `f`.
-/

namespace PoissonBinomialComparison

noncomputable section

/-- The density `g(t)` in the manuscript's dimension-improvement argument. -/
def switchRhoDensity (n j : ℕ) (a b t : ℝ) : ℝ :=
  switchRho n j a b * pbMass (fun _ : Fin (n - 1) ↦ t) (j - 1) +
    (1 - switchRho n j a b) * pbMass (fun _ : Fin (n - 1) ↦ t) j

/-- The explicit mixture is exactly the mass after adjoining a Bernoulli `rho`. -/
theorem switchRhoDensity_eq_pbMass_cons (n j : ℕ) (hj : 0 < j) (a b t : ℝ) :
    switchRhoDensity n j a b t =
      pbMass (Fin.cons (switchRho n j a b) (fun _ : Fin (n - 1) ↦ t)) j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  have h := pbMassInt_cons (fun _ : Fin (n - 1) ↦ t) (switchRho n (k + 1) a b)
    ((k + 1 : ℕ) : ℤ)
  have hk : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
  simp only [hk, pbMassIntOn_natCast] at h
  simp only [switchRhoDensity, Nat.succ_eq_add_one, Nat.add_sub_cancel, pbMass]
  rw [h]
  ring

/-- The lower adjacent deleted-binomial mass as a multiple of the original mass. -/
theorem pbMass_const_deleted_lower {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {t : ℝ} (ht : t ≠ 0) :
    pbMass (fun _ : Fin (n - 1) ↦ t) (j - 1) =
      (j : ℝ) * pbMass (fun _ : Fin n ↦ t) j / ((n : ℝ) * t) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hcoeff : (n : ℝ) * ((n - 1).choose (j - 1) : ℝ) = (n.choose j : ℝ) * j := by
    have hh := Nat.add_one_mul_choose_eq (n - 1) (j - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.sub_add_cancel (by omega : 1 ≤ j)] at hh
    exact_mod_cast hh
  have hexp : n - 1 - (j - 1) = n - j := by omega
  have hpow : t ^ j = t ^ (j - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  apply (eq_div_iff (mul_ne_zero hn ht)).mpr
  simp only [pbMass_const, hexp, hpow]
  linear_combination (t ^ (j - 1) * (1 - t) ^ (n - j) * t) * hcoeff

/-- The upper adjacent deleted-binomial mass as a multiple of the original mass. -/
theorem pbMass_const_deleted_upper {n j : ℕ} (hjn : j < n)
    {t : ℝ} (ht : 1 - t ≠ 0) :
    pbMass (fun _ : Fin (n - 1) ↦ t) j =
      ((n - j : ℕ) : ℝ) * pbMass (fun _ : Fin n ↦ t) j / ((n : ℝ) * (1 - t)) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hcoeff : ((n - 1).choose j : ℝ) * n = (n.choose j : ℝ) * (n - j : ℕ) := by
    have hh := Nat.choose_mul_succ_eq (n - 1) j
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hh
    exact_mod_cast hh
  have hexp : n - 1 - j + 1 = n - j := by omega
  have hpow : (1 - t) ^ (n - j) = (1 - t) ^ (n - 1 - j) * (1 - t) := by
    rw [← pow_succ, hexp]
  apply (eq_div_iff (mul_ne_zero hn ht)).mpr
  simp only [pbMass_const, hpow]
  linear_combination (t ^ j * (1 - t) ^ (n - 1 - j) * (1 - t)) * hcoeff

private theorem rho_density_algebra (c a b f : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : 1 - a ≠ 0) (hb1 : 1 - b ≠ 0)
    (hc : c * (1 - c) ≠ 0)
    (hD : c * (1 - a) * (1 - b) + (1 - c) * a * b ≠ 0) :
    let r := (1 - c) * a * b / (c * (1 - a) * (1 - b) + (1 - c) * a * b)
    let R := (a - c) * (c - b) / (c * (1 - c))
    (r * (c * f / a) + (1 - r) * ((1 - c) * f / (1 - a)) = f / (1 - R)) ∧
      (r * (c * f / b) + (1 - r) * ((1 - c) * f / (1 - b)) = f / (1 - R)) := by
  dsimp
  have hR : 1 - (a - c) * (c - b) / (c * (1 - c)) =
      (c * (1 - a) * (1 - b) + (1 - c) * a * b) / (c * (1 - c)) := by
    apply (eq_div_iff hc).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hc]
    exact switch_denominator_identity c a b
  rw [hR]
  constructor <;> field_simp <;> ring

/-- The adjoined parameter rewritten using the normalized switching count. -/
theorem switchRho_eq_normalized {n j : ℕ} (hjn : j ≤ n) (hn : 0 < n) (a b : ℝ) :
    switchRho n j a b =
      (1 - (j : ℝ) / n) * a * b /
        (((j : ℝ) / n) * (1 - a) * (1 - b) + (1 - (j : ℝ) / n) * a * b) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold switchRho
  rw [Nat.cast_sub hjn]
  field_simp
  ring

/-- The exact density identity at both parameters of an arbitrary interior switch. -/
theorem IsSwitch.rhoDensity_eq {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b)
    (hj : 0 < j) (hjn : j < n) :
    let c := (j : ℝ) / n
    let R := (a - c) * (c - b) / (c * (1 - c))
    let f := pbMass (fun _ : Fin n ↦ a) j
    switchRhoDensity n j a b a = f / (1 - R) ∧
      switchRhoDensity n j a b b = f / (1 - R) := by
  dsimp
  have ha : 0 < a := h.1.trans h.2.1
  have ha1 : 0 < 1 - a := sub_pos.mpr h.2.2.1
  have hb1 : 0 < 1 - b := sub_pos.mpr (h.2.1.trans h.2.2.1)
  have hc := h.center_bounds hj hjn
  have hcv : ((j : ℝ) / n) * (1 - (j : ℝ) / n) ≠ 0 :=
    (mul_pos (h.1.trans hc.1) (by linarith [hc.2, h.2.2.1])).ne'
  have hh := rho_density_algebra ((j : ℝ) / n) a b (pbMass (fun _ : Fin n ↦ a) j)
    ha.ne' h.1.ne' ha1.ne' hb1.ne' hcv (h.denominator_pos hj hjn).ne'
  dsimp at hh
  unfold switchRhoDensity
  rw [pbMass_const_deleted_lower hj hjn ha.ne', pbMass_const_deleted_upper hjn ha1.ne',
    pbMass_const_deleted_lower hj hjn h.1.ne', pbMass_const_deleted_upper hjn hb1.ne',
    ← h.pbMass_eq, switchRho_eq_normalized hjn.le (by omega), Nat.cast_sub hjn.le]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hleft (x f : ℝ) : (j : ℝ) * f / ((n : ℝ) * x) = ((j : ℝ) / n) * f / x := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hright (x f : ℝ) : ((n : ℝ) - j) * f / ((n : ℝ) * (1 - x)) =
      (1 - (j : ℝ) / n) * f / (1 - x) := by
    have hc' : ((n : ℝ) - j) / n = 1 - (j : ℝ) / n := by field_simp
    calc
      _ = (((n : ℝ) - j) / n) * f / (1 - x) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [hc']
  simp only [hleft, hright]
  exact hh

/-- Canonical-switch version of the density identity, with exactly `switchMass/(1-R)`. -/
theorem switchRhoDensity_eq_switchMass {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchRhoDensity n j (switchUpper n j γ) (switchLower n j γ) (switchUpper n j γ) =
        switchMass n j γ / (1 - switchRatio n j γ) ∧
      switchRhoDensity n j (switchUpper n j γ) (switchLower n j γ) (switchLower n j γ) =
        switchMass n j γ / (1 - switchRatio n j γ) :=
  (switchPair_spec hj hjn hγ0 hγ1).rhoDensity_eq hj hjn

/-- The perturbation's active-tail derivative is strictly negative. -/
theorem switchRhoDensity_improvement_neg {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchMass n j γ -
      (switchRhoDensity n j (switchUpper n j γ) (switchLower n j γ) (switchUpper n j γ) +
        switchRhoDensity n j (switchUpper n j γ) (switchLower n j γ) (switchLower n j γ)) / 2 < 0 := by
  obtain ⟨ha, hb⟩ := switchRhoDensity_eq_switchMass hj hjn hγ0 hγ1
  rw [ha, hb]
  have hf := switchMass_pos hj hjn hγ0 hγ1
  have hR := switchRatio_bounds hj hjn hγ0 hγ1
  have hlt : switchMass n j γ < switchMass n j γ / (1 - switchRatio n j γ) := by
    apply (lt_div_iff₀ (sub_pos.mpr hR.2)).mpr
    nlinarith
  linarith

end

end PoissonBinomialComparison
