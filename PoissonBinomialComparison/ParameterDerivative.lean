import PoissonBinomialComparison.RandomizedThreshold
import PoissonBinomialComparison.Compactness
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Derivatives in the individual parameters

The exact affine identities for the subset-sum model determine its full
Fréchet derivative. These interfaces apply to arbitrary differentiable curves,
including the constrained perturbations used in the optimization arguments.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ}

private theorem differentiable_product {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → (Fin n → ℝ) → ℝ) (h : ∀ i ∈ s, Differentiable ℝ (f i)) :
    Differentiable ℝ (fun p ↦ ∏ i ∈ s, f i p) := by
  intro p
  exact (HasFDerivAt.finsetProd (fun i hi ↦ (h i hi p).hasFDerivAt)).differentiableAt

@[fun_prop] theorem differentiable_bernoulliWeight (s A : Finset (Fin n)) :
    Differentiable ℝ (fun p ↦ bernoulliWeight p s A) := by
  exact (differentiable_product A (fun i p ↦ p i) (by intros; fun_prop)).mul
    (differentiable_product (s \ A) (fun i p ↦ 1-p i) (by intros; fun_prop))

@[fun_prop] theorem differentiable_pbMass (k : ℕ) :
    Differentiable ℝ (fun p : Fin n → ℝ ↦ pbMass p k) := by
  unfold pbMass pbMassOn
  fun_prop

@[fun_prop] theorem differentiable_pbTail (k : ℕ) :
    Differentiable ℝ (fun p : Fin n → ℝ ↦ pbTail p k) := by
  unfold pbTail pbTailOn
  apply Differentiable.fun_sum
  intro A _
  split_ifs <;> fun_prop

@[fun_prop] theorem differentiable_randomizedTail (w : ℝ) (k : ℕ) :
    Differentiable ℝ (fun p : Fin n → ℝ ↦ randomizedTail p w k) := by
  change Differentiable ℝ (fun p : Fin n → ℝ ↦ w * pbTail p k + (1-w)*pbTail p (k+1))
  fun_prop

/-- The algebraic coordinate coefficient is also the analytic partial derivative. -/
theorem hasDerivAt_randomizedTail_update (p : Fin n → ℝ) (i : Fin n)
    (w : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun t ↦ randomizedTail (Function.update p i t) w k)
      (randomizedGradient p w k i) x := by
  have heq : (fun t ↦ randomizedTail (Function.update p i t) w k) =
      (fun t ↦ randomizedTail p w k + (t-p i)*randomizedGradient p w k i) := by
    funext t
    have h := randomizedTail_update_sub p i (p i) t w k
    rw [Function.update_eq_self] at h
    linarith
  rw [heq]
  convert ((hasDerivAt_id x).sub_const (p i)).mul_const
    (randomizedGradient p w k i) |>.const_add (randomizedTail p w k) using 1 <;> simp

/-- Evaluation of the full derivative on a coordinate basis vector. -/
theorem fderiv_randomizedTail_single (p : Fin n → ℝ) (i : Fin n) (w : ℝ) (k : ℕ) :
    fderiv ℝ (fun q ↦ randomizedTail q w k) p (Pi.single i 1) =
      randomizedGradient p w k i := by
  have h := ((differentiable_randomizedTail (n := n) w k) p).hasFDerivAt
  have hc := h.comp_hasDerivAt_of_eq (p i) (hasDerivAt_update p i (p i))
    (Function.update_eq_self i p).symm
  exact hc.unique (hasDerivAt_randomizedTail_update p i w k (p i))

/-- The gradient formula in any direction, without parameter-range assumptions. -/
theorem fderiv_randomizedTail_apply (p v : Fin n → ℝ) (w : ℝ) (k : ℕ) :
    fderiv ℝ (fun q ↦ randomizedTail q w k) p v =
      ∑ i, v i * randomizedGradient p w k i := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, smul_eq_mul, fderiv_randomizedTail_single]

/-- Chain rule along an arbitrary differentiable parameter curve. -/
theorem hasDerivAt_randomizedTail_curve {p : ℝ → Fin n → ℝ} {v : Fin n → ℝ}
    {t : ℝ} (hp : HasDerivAt p v t) (w : ℝ) (k : ℕ) :
    HasDerivAt (fun x ↦ randomizedTail (p x) w k)
      (∑ i, v i * randomizedGradient (p t) w k i) t := by
  simpa only [Function.comp_def, fderiv_randomizedTail_apply] using
    (((differentiable_randomizedTail (n := n) w k) (p t)).hasFDerivAt.comp_hasDerivAt t hp)

/-- Derivative of the difference of randomized tests along two parameter curves. -/
theorem hasDerivAt_randomizedDiff_curve {p q : ℝ → Fin n → ℝ}
    {u v : Fin n → ℝ} {t : ℝ} (hp : HasDerivAt p u t) (hq : HasDerivAt q v t)
    (w : ℝ) (k : ℕ) :
    HasDerivAt (fun x ↦ randomizedTail (p x) w k - randomizedTail (q x) w k)
      (∑ i, (u i * randomizedGradient (p t) w k i -
        v i * randomizedGradient (q t) w k i)) t := by
  convert! (hasDerivAt_randomizedTail_curve hp w k).sub
    (hasDerivAt_randomizedTail_curve hq w k) using 1
  simp [sum_sub_distrib]

@[fun_prop] theorem differentiable_tailDiff (k : ℕ) :
    Differentiable ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailDiff x.1 x.2 k) := by
  unfold tailDiff
  fun_prop

/-- The randomized difference is exactly the convex combination of adjacent
threshold differences, including endpoint randomization weights. -/
theorem randomizedDiff_eq (p q : Fin n → ℝ) (w : ℝ) (k : ℕ) :
    randomizedTail p w k - randomizedTail q w k =
      w*tailDiff p q k + (1-w)*tailDiff p q (k+1) := by
  unfold randomizedTail randomizedTailOn tailDiff pbTail
  ring

/-- The weighted active gradient is exactly the manuscript's randomized gradient. -/
theorem weighted_fderiv_tailDiff_apply (p q u v : Fin n → ℝ) (w : ℝ) (k : ℕ) :
    w * fderiv ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailDiff x.1 x.2 k) (p,q) (u,v) +
      (1-w) * fderiv ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailDiff x.1 x.2 (k+1)) (p,q) (u,v) =
      ∑ i, (u i * randomizedGradient p w k i - v i * randomizedGradient q w k i) := by
  have hp : HasDerivAt (fun t : ℝ ↦ p+t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
  have hq : HasDerivAt (fun t : ℝ ↦ q+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hpath := hp.prodMk hq
  have hk := ((differentiable_tailDiff (n := n) k) (p,q)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have hk1 := ((differentiable_tailDiff (n := n) (k+1)) (p,q)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have hcomb := (hk.const_mul w).add (hk1.const_mul (1-w))
  have hrand := hasDerivAt_randomizedDiff_curve hp hq w k
  have heq : (fun t : ℝ ↦ w*tailDiff (p+t • u) (q+t • v) k +
      (1-w)*tailDiff (p+t • u) (q+t • v) (k+1)) =
      (fun t ↦ randomizedTail (p+t • u) w k-randomizedTail (q+t • v) w k) := by
    funext t
    exact (randomizedDiff_eq _ _ w k).symm
  change HasDerivAt (fun t : ℝ ↦ w*tailDiff (p+t • u) (q+t • v) k +
    (1-w)*tailDiff (p+t • u) (q+t • v) (k+1)) _ 0 at hcomb
  rw [heq] at hcomb
  simpa using hcomb.unique hrand

end

end PoissonBinomialComparison
