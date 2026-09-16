import PoissonBinomialComparison.SwitchDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Normalized switch-mass integrals

The derivative of `F(γ) + γ f(γ)` is `(n+1)f(γ)`. The fundamental theorem of
calculus applies on the closed gap interval using the proved continuous
endpoint extensions, so both endpoint cases are included explicitly.
-/

namespace PoissonBinomialComparison

open MeasureTheory

/-- The common switching mass is integrable between zero and any feasible gap. -/
theorem intervalIntegrable_switchMass {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    IntervalIntegrable (switchMass n j) volume 0 γ :=
  ((continuousOn_switchMass hj hjn).mono (Set.Icc_subset_Icc le_rfl hγ1)).intervalIntegrable_of_Icc hγ0

/-- The differential form of the normalized switch-mass identity. -/
theorem hasDerivAt_switchValue_add_mul_mass {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    HasDerivAt (fun u ↦ switchValue n j u + u * switchMass n j u)
      (((n : ℝ) + 1) * switchMass n j γ) γ := by
  have hF := (hasDerivAt_switchValue hj hjn hγ0 hγ1).differentiableAt.hasDerivAt
  have hf := (hasDerivAt_switchMass hj hjn hγ0 hγ1).differentiableAt.hasDerivAt
  convert hF.add ((hasDerivAt_id γ).mul hf) using 1
  · rfl
  · rw [deriv_switchValue_eq_mass_sub hj hjn hγ0 hγ1]
    simp only [id_eq]
    ring

/-- The manuscript's exact normalized switch-mass formula, including both endpoints. -/
theorem switchValue_eq_integral_mass {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    switchValue n j γ = ((n : ℝ) + 1) * (∫ u in (0 : ℝ)..γ, switchMass n j u) -
      γ * switchMass n j γ := by
  have hF := (continuousOn_switchValue hj hjn).mono (Set.Icc_subset_Icc le_rfl hγ1)
  have hf := (continuousOn_switchMass hj hjn).mono (Set.Icc_subset_Icc le_rfl hγ1)
  have hcont : ContinuousOn (fun u ↦ switchValue n j u + u * switchMass n j u)
      (Set.Icc 0 γ) := hF.add (continuousOn_id.mul hf)
  have hint : IntervalIntegrable (fun u ↦ ((n : ℝ) + 1) * switchMass n j u) volume 0 γ :=
    (intervalIntegrable_switchMass hj hjn hγ0 hγ1).const_mul _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hγ0 hcont
    (fun u hu ↦ hasDerivAt_switchValue_add_mul_mass hj hjn hu.1 (lt_of_lt_of_le hu.2 hγ1)) hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  simp only [switchValue_zero, zero_mul, add_zero, sub_zero] at hFTC
  linarith

/-- All switching masses have the same integral, independently of the switching count. -/
theorem integral_switchMass {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    (∫ u in (0 : ℝ)..1, switchMass n j u) = 1 / ((n : ℝ) + 1) := by
  have h := switchValue_eq_integral_mass hj hjn (γ := 1) zero_le_one le_rfl
  rw [switchValue_one hj hjn.le, switchMass_one hjn] at h
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  apply (eq_div_iff hn).2
  linarith

end PoissonBinomialComparison
