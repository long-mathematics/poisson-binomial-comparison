import PoissonBinomialComparison.Homogeneous
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The central integer-mean binomial atom bound

The manuscript's comparison of integer-mean binomial atoms uses the increasing
function `h(x) = x log(1 + 1/x)`. Factoring atoms through `m^m / m!` keeps
all factors strictly positive, including the deterministic case `m = 0`.
-/

namespace PoissonBinomialComparison

open scoped BigOperators

noncomputable section

/-- The mass of `Bin(M, ℓ/M)` at its integer mean `ℓ`.
At `M = ℓ = 0` the displayed finite formula gives one. -/
def integerMeanBinomialMass (M ℓ : ℕ) : ℝ :=
  (M.choose ℓ : ℝ) * ((ℓ : ℝ) / M) ^ ℓ * (1 - (ℓ : ℝ) / M) ^ (M - ℓ)

/-- The manuscript's central integer-mean binomial atom constant. -/
def kappa (n : ℕ) : ℝ := integerMeanBinomialMass n (n / 2)

/-- The logarithmic increment `h`, with its value zero at zero automatic. -/
def atomLogIncrement (x : ℝ) : ℝ := x * Real.log (1 + x⁻¹)

private def atomFactor (m : ℕ) : ℝ := (m : ℝ) ^ m / (m.factorial : ℝ)

private theorem atomFactor_pos (m : ℕ) : 0 < atomFactor m := by
  cases m with
  | zero => norm_num [atomFactor]
  | succ m => unfold atomFactor; positivity

@[simp] theorem atomLogIncrement_zero : atomLogIncrement 0 = 0 := by
  simp [atomLogIncrement]

/-- Derivative of the auxiliary increasing function at a positive argument. -/
theorem hasDerivAt_atomLogIncrement {x : ℝ} (hx : 0 < x) :
    HasDerivAt atomLogIncrement (Real.log (1 + x⁻¹) - (x + 1)⁻¹) x := by
  have hxne := hx.ne'
  have hne : 1 + x⁻¹ ≠ 0 := by positivity
  have hd := (hasDerivAt_id x).mul (((hasDerivAt_inv hxne).const_add 1).log hne)
  convert hd using 1
  · rfl
  · simp only [one_mul, id_eq]
    field_simp
    ring

/-- The auxiliary function has nonnegative derivative on the positive half-line. -/
theorem atomLogIncrement_deriv_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ deriv atomLogIncrement x := by
  rw [(hasDerivAt_atomLogIncrement hx).deriv]
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x⁻¹ by positivity)
  have heq : 1 - (1 + x⁻¹)⁻¹ = (x + 1)⁻¹ := by
    have hxne := hx.ne'
    have hx1 : x + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [heq] at h
  exact sub_nonneg.mpr h

/-- The manuscript's monotonicity of `h`, including its boundary value zero. -/
theorem atomLogIncrement_mono : MonotoneOn atomLogIncrement (Set.Ici 0) := by
  have hmono : MonotoneOn atomLogIncrement (Set.Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro x hx
      exact (hasDerivAt_atomLogIncrement hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_atomLogIncrement (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      exact atomLogIncrement_deriv_nonneg (interior_subset hx)
  intro x hx y hy hxy
  by_cases hx0 : x = 0
  · subst x
    rw [atomLogIncrement_zero]
    exact mul_nonneg hy (Real.log_nonneg (by have := inv_nonneg.mpr (show 0 ≤ y from hy); linarith))
  · exact hmono (lt_of_le_of_ne hx (Ne.symm hx0))
      ((lt_of_le_of_ne hx (Ne.symm hx0)).trans_le hxy) hxy

private theorem atomLogIncrement_nat (m : ℕ) :
    atomLogIncrement m = (m : ℝ) * (Real.log (m + 1) - Real.log m) := by
  cases m with
  | zero => simp
  | succ m =>
    have hm : (m + 1 : ℝ) ≠ 0 := by positivity
    have hid : 1 + (m + 1 : ℝ)⁻¹ = ((m + 1 : ℝ) + 1) / (m + 1 : ℝ) := by
      field_simp
    simp only [atomLogIncrement, Nat.cast_add, Nat.cast_one]
    rw [hid, Real.log_div (by positivity) hm]

private theorem log_atomFactor_succ (m : ℕ) :
    Real.log (atomFactor (m + 1)) - Real.log (atomFactor m) = atomLogIncrement m := by
  have hmfact : (m.factorial : ℝ) ≠ 0 := by positivity
  have hm1fact : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
  have hpow : (m : ℝ) ^ m ≠ 0 := by
    cases m with
    | zero => simp
    | succ m => positivity
  have hpow1 : ((m + 1 : ℕ) : ℝ) ^ (m + 1) ≠ 0 := by positivity
  rw [atomFactor, atomFactor, Real.log_div hpow1 hm1fact, Real.log_div hpow hmfact,
    Real.log_pow, Real.log_pow, Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) hmfact, atomLogIncrement_nat]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- The mass formula agrees with the homogeneous subset-sum probability. -/
theorem integerMeanBinomialMass_eq_pbMass (M ℓ : ℕ) :
    integerMeanBinomialMass M ℓ = pbMass (fun _ : Fin M ↦ (ℓ : ℝ) / M) ℓ := by
  rw [pbMass_const]
  rfl

private theorem integerMeanBinomialMass_factor {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    integerMeanBinomialMass M ℓ = atomFactor ℓ * atomFactor (M - ℓ) / atomFactor M := by
  by_cases hM : M = 0
  · subst M
    have hℓ0 : ℓ = 0 := by omega
    subst ℓ
    norm_num [integerMeanBinomialMass, atomFactor]
  have hMn : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have hMpow : (M : ℝ) ^ M ≠ 0 := pow_ne_zero M hMn
  have hlfact : (ℓ.factorial : ℝ) ≠ 0 := by positivity
  have hrfact : ((M - ℓ).factorial : ℝ) ≠ 0 := by positivity
  have hMfact : (M.factorial : ℝ) ≠ 0 := by positivity
  have hfactor : (M.choose ℓ : ℝ) * (ℓ.factorial : ℝ) * ((M - ℓ).factorial : ℝ) = M.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hℓ
  have hchoose : (M.choose ℓ : ℝ) = (M.factorial : ℝ) /
      ((ℓ.factorial : ℝ) * ((M - ℓ).factorial : ℝ)) := by
    apply (eq_div_iff (mul_ne_zero hlfact hrfact)).mpr
    simpa only [mul_assoc] using hfactor
  have hfrac : 1 - (ℓ : ℝ) / M = ((M - ℓ : ℕ) : ℝ) / M := by
    rw [Nat.cast_sub hℓ]
    field_simp
  have hpower : (M : ℝ) ^ ℓ * (M : ℝ) ^ (M - ℓ) = (M : ℝ) ^ M := by
    rw [← pow_add, Nat.add_sub_of_le hℓ]
  unfold integerMeanBinomialMass atomFactor
  rw [hchoose, hfrac, div_pow, div_pow]
  field_simp
  rw [← hpower]
  ring

/-- Integer-mean binomial atoms are strictly positive, including deterministic endpoints. -/
theorem integerMeanBinomialMass_pos {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    0 < integerMeanBinomialMass M ℓ := by
  rw [integerMeanBinomialMass_factor hℓ]
  exact div_pos (mul_pos (atomFactor_pos ℓ) (atomFactor_pos (M - ℓ))) (atomFactor_pos M)

private theorem log_integerMeanBinomialMass {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    Real.log (integerMeanBinomialMass M ℓ) =
      Real.log (atomFactor ℓ) + Real.log (atomFactor (M - ℓ)) - Real.log (atomFactor M) := by
  rw [integerMeanBinomialMass_factor hℓ,
    Real.log_div (mul_ne_zero (atomFactor_pos ℓ).ne' (atomFactor_pos (M - ℓ)).ne')
      (atomFactor_pos M).ne', Real.log_mul (atomFactor_pos ℓ).ne' (atomFactor_pos (M - ℓ)).ne']

/-- First manuscript log-ratio identity, in subtraction form to avoid division. -/
theorem integerMeanBinomialMass_log_step_count {M ℓ : ℕ} (hℓ : ℓ + 1 ≤ M) :
    Real.log (integerMeanBinomialMass M ℓ) - Real.log (integerMeanBinomialMass M (ℓ + 1)) =
      atomLogIncrement (M - ℓ - 1 : ℕ) - atomLogIncrement ℓ := by
  rw [log_integerMeanBinomialMass (by omega), log_integerMeanBinomialMass hℓ]
  have h1 := log_atomFactor_succ ℓ
  have h2 := log_atomFactor_succ (M - ℓ - 1)
  have hr : M - ℓ - 1 + 1 = M - ℓ := by omega
  have hr' : M - (ℓ + 1) = M - ℓ - 1 := by omega
  rw [hr] at h2
  rw [hr']
  linarith

/-- Second manuscript log-ratio identity. -/
theorem integerMeanBinomialMass_log_step_dimension {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    Real.log (integerMeanBinomialMass (M + 1) ℓ) - Real.log (integerMeanBinomialMass M ℓ) =
      atomLogIncrement (M - ℓ : ℕ) - atomLogIncrement M := by
  rw [log_integerMeanBinomialMass (by omega), log_integerMeanBinomialMass hℓ]
  have h1 := log_atomFactor_succ M
  have h2 := log_atomFactor_succ (M - ℓ)
  have hr : M + 1 - ℓ = (M - ℓ) + 1 := by omega
  rw [hr]
  linarith

/-- The two complementary integer means give the same binomial atom. -/
theorem integerMeanBinomialMass_symm {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    integerMeanBinomialMass M (M - ℓ) = integerMeanBinomialMass M ℓ := by
  rw [integerMeanBinomialMass_factor (by omega), integerMeanBinomialMass_factor hℓ,
    Nat.sub_sub_self hℓ]
  ring

/-- Moving the integer mean toward the center can only decrease the atom. -/
theorem integerMeanBinomialMass_succ_count_le {M ℓ : ℕ} (hℓ : ℓ < M / 2) :
    integerMeanBinomialMass M (ℓ + 1) ≤ integerMeanBinomialMass M ℓ := by
  have hℓM : ℓ + 1 ≤ M := by omega
  apply (Real.log_le_log_iff (integerMeanBinomialMass_pos hℓM)
    (integerMeanBinomialMass_pos (by omega))).mp
  have h := integerMeanBinomialMass_log_step_count hℓM
  have hinc : atomLogIncrement (ℓ : ℝ) ≤ atomLogIncrement ((M - ℓ - 1 : ℕ) : ℝ) := by
    apply atomLogIncrement_mono (by simp) (by simp)
    exact_mod_cast (show ℓ ≤ M - ℓ - 1 by omega)
  linarith

private theorem integerMeanBinomialMass_central_le_of_le_half {M ℓ : ℕ}
    (hℓ : ℓ ≤ M / 2) : integerMeanBinomialMass M (M / 2) ≤ integerMeanBinomialMass M ℓ := by
  by_cases heq : ℓ = M / 2
  · simp [heq]
  · have hlt : ℓ < M / 2 := by omega
    exact (integerMeanBinomialMass_central_le_of_le_half (ℓ := ℓ + 1) (by omega)).trans
      (integerMeanBinomialMass_succ_count_le hlt)
termination_by M / 2 - ℓ
decreasing_by omega

/-- The central integer-mean atom is the smallest at a fixed dimension. -/
theorem kappa_le_integerMeanBinomialMass {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    kappa M ≤ integerMeanBinomialMass M ℓ := by
  unfold kappa
  by_cases hhalf : ℓ ≤ M / 2
  · exact integerMeanBinomialMass_central_le_of_le_half hhalf
  · have hother : M - ℓ ≤ M / 2 := by omega
    simpa only [integerMeanBinomialMass_symm hℓ] using
      integerMeanBinomialMass_central_le_of_le_half hother

/-- Increasing the dimension at fixed integer mean can only decrease the atom. -/
theorem integerMeanBinomialMass_succ_dimension_le {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    integerMeanBinomialMass (M + 1) ℓ ≤ integerMeanBinomialMass M ℓ := by
  apply (Real.log_le_log_iff (integerMeanBinomialMass_pos (by omega))
    (integerMeanBinomialMass_pos hℓ)).mp
  have h := integerMeanBinomialMass_log_step_dimension hℓ
  have hinc : atomLogIncrement ((M - ℓ : ℕ) : ℝ) ≤ atomLogIncrement (M : ℝ) := by
    apply atomLogIncrement_mono (by simp) (by simp)
    exact_mod_cast Nat.sub_le M ℓ
  linarith

/-- Dimension monotonicity for any number of extra trials. -/
theorem integerMeanBinomialMass_antitone_dimension {M n ℓ : ℕ}
    (hℓ : ℓ ≤ M) (hMn : M ≤ n) :
    integerMeanBinomialMass n ℓ ≤ integerMeanBinomialMass M ℓ := by
  have hanti : AntitoneOn (fun j ↦ integerMeanBinomialMass j ℓ) (Set.Ici ℓ) :=
    antitoneOn_nat_Ici_of_succ_le (fun j hj ↦ integerMeanBinomialMass_succ_dimension_le hj)
  exact hanti hℓ (hℓ.trans hMn) hMn

/-- The numerical inequality needed by the manuscript's integer-mean atom bound.
It includes `M = 0`, where the right-hand side is one. -/
theorem kappa_le_integerMeanBinomialMass_of_le {n M ℓ : ℕ}
    (hℓ : ℓ ≤ M) (hMn : M ≤ n) :
    kappa n ≤ integerMeanBinomialMass M ℓ :=
  (kappa_le_integerMeanBinomialMass (hℓ.trans hMn)).trans
    (integerMeanBinomialMass_antitone_dimension hℓ hMn)

/-- The same numerical bound directly in the subset-sum mass representation. -/
theorem kappa_le_pbMass_integerMean {n M ℓ : ℕ} (hℓ : ℓ ≤ M) (hMn : M ≤ n) :
    kappa n ≤ pbMass (fun _ : Fin M ↦ (ℓ : ℝ) / M) ℓ := by
  rw [← integerMeanBinomialMass_eq_pbMass]
  exact kappa_le_integerMeanBinomialMass_of_le hℓ hMn

/-- Positivity of the manuscript atom constant. -/
theorem kappa_pos (n : ℕ) : 0 < kappa n :=
  integerMeanBinomialMass_pos (Nat.div_le_self n 2)

/-- The atom constant is at most the deterministic mass one. -/
theorem kappa_le_one (n : ℕ) : kappa n ≤ 1 := by
  have h := kappa_le_integerMeanBinomialMass_of_le (n := n) (M := 0) (ℓ := 0)
    (by omega) (by omega)
  simpa [integerMeanBinomialMass] using h

/-- Exact agreement with the manuscript's floor/ceiling formula.
For natural dimensions `(n + 1) / 2` is the ceiling of `n / 2`. -/
theorem kappa_eq_formula {n : ℕ} (hn : 0 < n) :
    kappa n = (n.choose (n / 2) : ℝ) * (((n / 2 : ℕ) : ℝ) / n) ^ (n / 2) *
      ((((n + 1) / 2 : ℕ) : ℝ) / n) ^ ((n + 1) / 2) := by
  have hsub : n - n / 2 = (n + 1) / 2 := by omega
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hfrac : 1 - ((n / 2 : ℕ) : ℝ) / n = (((n + 1) / 2 : ℕ) : ℝ) / n := by
    rw [← hsub, Nat.cast_sub (Nat.div_le_self n 2)]
    field_simp
  simp only [kappa, integerMeanBinomialMass, hsub, hfrac]

end

end PoissonBinomialComparison
