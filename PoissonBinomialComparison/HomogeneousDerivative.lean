import PoissonBinomialComparison.Homogeneous
import PoissonBinomialComparison.Coordinate
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Derivatives of homogeneous tails

The subset-sum mass is the evaluation of a Bernstein polynomial. Existing
mathlib polynomial derivative identities therefore give the mass derivatives.
Subtracting successive masses from the upper tail telescopes these derivatives,
giving the manuscript's binomial-tail density formula without division.
-/

namespace PoissonBinomialComparison

/-- The homogeneous subset-sum mass is a Bernstein polynomial evaluation. -/
theorem pbMass_const_eq_bernstein_eval (n k : ℕ) (t : ℝ) :
    pbMass (fun _ : Fin n ↦ t) k = (bernsteinPolynomial ℝ n k).eval t := by
  simp [pbMass_const, bernsteinPolynomial]

/-- Derivative of the mass at zero, including dimension zero. -/
theorem hasDerivAt_pbMass_const_zero (n : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ pbMass (fun _ : Fin n ↦ u) 0)
      (-(n : ℝ) * pbMass (fun _ : Fin (n - 1) ↦ t) 0) t := by
  simpa only [pbMass_const_eq_bernstein_eval, bernsteinPolynomial.derivative_zero,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_natCast] using
    (bernsteinPolynomial ℝ n 0).hasDerivAt t

/-- Derivative of each positive-count homogeneous mass. -/
theorem hasDerivAt_pbMass_const_succ (n k : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ pbMass (fun _ : Fin n ↦ u) (k + 1))
      ((n : ℝ) * (pbMass (fun _ : Fin (n - 1) ↦ t) k -
        pbMass (fun _ : Fin (n - 1) ↦ t) (k + 1))) t := by
  simpa only [pbMass_const_eq_bernstein_eval, bernsteinPolynomial.derivative_succ,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_natCast] using
    (bernsteinPolynomial ℝ n (k + 1)).hasDerivAt t

/-- The homogeneous upper-tail derivative is dimension times the deleted-coordinate
mass. The formula also handles dimensions zero and thresholds above the support. -/
theorem hasDerivAt_pbTail_const_succ (n k : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ pbTail (fun _ : Fin n ↦ u) (k + 1))
      ((n : ℝ) * pbMass (fun _ : Fin (n - 1) ↦ t) k) t := by
  induction k with
  | zero =>
    have hd := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_pbMass_const_zero n t)
    convert hd using 1
    · funext u
      simp only [Pi.sub_apply, zero_add]
      have h := pbTail_sub_succ (fun _ : Fin n ↦ u) 0
      simp only [pbTail_zero, zero_add] at h
      linarith
    · ring
  | succ k ih =>
    have hd := ih.sub (hasDerivAt_pbMass_const_succ n k t)
    convert hd using 1
    · funext u
      simp only [Pi.sub_apply]
      have h := pbTail_sub_succ (fun _ : Fin n ↦ u) (k + 1)
      linarith
    · ring

/-- The manuscript's tail-density formula at an arbitrary positive threshold. -/
theorem hasDerivAt_pbTail_const (n k : ℕ) (hk : 0 < k) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ pbTail (fun _ : Fin n ↦ u) k)
      ((n : ℝ) * pbMass (fun _ : Fin (n - 1) ↦ t) (k - 1)) t := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simpa using hasDerivAt_pbTail_const_succ n j t

/-- The same derivative with its binomial density expanded, as in the manuscript. -/
theorem hasDerivAt_pbTail_const_density (n k : ℕ) (hk : 0 < k) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ pbTail (fun _ : Fin n ↦ u) k)
      ((n : ℝ) * ((n - 1).choose (k - 1) : ℝ) *
        t ^ (k - 1) * (1 - t) ^ (n - k)) t := by
  convert hasDerivAt_pbTail_const n k hk t using 1
  rw [pbMass_const]
  have hexp : n - 1 - (k - 1) = n - k := by omega
  rw [hexp]
  ring

/-- A rewriting interface for the derivative of the homogeneous tail. -/
theorem deriv_pbTail_const (n k : ℕ) (hk : 0 < k) (t : ℝ) :
    deriv (fun u : ℝ ↦ pbTail (fun _ : Fin n ↦ u) k) t =
      (n : ℝ) * pbMass (fun _ : Fin (n - 1) ↦ t) (k - 1) :=
  (hasDerivAt_pbTail_const n k hk t).deriv

/-- At a switch, the two adjacent threshold differences agree exactly. -/
theorem IsSwitch.tailDiff_eq {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b) :
    tailDiff (fun _ : Fin n ↦ a) (fun _ : Fin n ↦ b) j =
      tailDiff (fun _ : Fin n ↦ a) (fun _ : Fin n ↦ b) (j + 1) := by
  have ha := pbTail_sub_succ (fun _ : Fin n ↦ a) j
  have hb := pbTail_sub_succ (fun _ : Fin n ↦ b) j
  have hm := h.pbMass_eq
  unfold tailDiff
  linarith

end PoissonBinomialComparison
