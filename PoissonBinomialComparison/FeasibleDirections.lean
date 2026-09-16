import PoissonBinomialComparison.Compactness
import Mathlib.Analysis.Convex.Basic

/-!
# Feasible directions for the ordered parameter polytope

The three coordinate inequalities are `q ≥ 0`, `p-q ≥ 0`, and `1-p ≥ 0`.
Their active-face signs, together with the linear mean constraint, describe
exact positive feasible rays. No constraint qualification is assumed.
-/

namespace PoissonBinomialComparison

open scoped BigOperators Topology
open Finset Filter

/-- Linearized feasible directions at an ordered pair of a fixed mean gap. -/
def feasibleDirections {n : ℕ} (p q : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {d | (∑ i, (d.1 i-d.2 i)) = 0 ∧ ∀ i,
    (p i = 1 → d.1 i ≤ 0) ∧ (q i = 0 → 0 ≤ d.2 i) ∧
      (p i = q i → d.2 i ≤ d.1 i)}

theorem zero_mem_feasibleDirections {n : ℕ} (p q : Fin n → ℝ) :
    0 ∈ feasibleDirections p q := by
  simp [feasibleDirections]

/-- The direction set is convex, including at intersections of boundary faces. -/
theorem convex_feasibleDirections {n : ℕ} (p q : Fin n → ℝ) :
    Convex ℝ (feasibleDirections p q) := by
  intro x hx y hy a b ha hb _
  constructor
  · change ∑ i, (a*x.1 i+b*y.1 i-(a*x.2 i+b*y.2 i)) = 0
    simp_rw [show ∀ i, a*x.1 i+b*y.1 i-(a*x.2 i+b*y.2 i) =
      a*(x.1 i-x.2 i)+b*(y.1 i-y.2 i) by intro i; ring]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hx.1, hy.1]
    ring
  · intro i
    change (p i = 1 → a*x.1 i+b*y.1 i ≤ 0) ∧
      (q i = 0 → 0 ≤ a*x.2 i+b*y.2 i) ∧
      (p i = q i → a*x.2 i+b*y.2 i ≤ a*x.1 i+b*y.1 i)
    exact ⟨fun h ↦ add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha ((hx.2 i).1 h))
      (mul_nonpos_of_nonneg_of_nonpos hb ((hy.2 i).1 h)),
      fun h ↦ add_nonneg (mul_nonneg ha ((hx.2 i).2.1 h))
        (mul_nonneg hb ((hy.2 i).2.1 h)),
      fun h ↦ add_le_add (mul_le_mul_of_nonneg_left ((hx.2 i).2.2 h) ha)
        (mul_le_mul_of_nonneg_left ((hy.2 i).2.2 h) hb)⟩

/-- An affine inequality holds along small positive steps exactly when its
slope points inward at an active boundary. -/
theorem eventually_nonneg_affine {a b : ℝ} (ha : 0 ≤ a) (hb : a = 0 → 0 ≤ b) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ a+t*b := by
  rcases ha.eq_or_lt with h | h
  · have ha0 : a = 0 := h.symm
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact by simpa [ha0] using mul_nonneg (le_of_lt ht) (hb ha0)
  · have hc : ContinuousAt (fun t : ℝ ↦ a+t*b) 0 := by fun_prop
    have he := hc.eventually (eventually_gt_nhds (by simpa using h))
    have he' : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < a+t*b := he.filter_mono nhdsWithin_le_nhds
    exact he'.mono (fun _ ht ↦ ht.le)

/-- Every direction satisfying the active-face signs produces genuinely feasible
ordered parameters for all sufficiently small positive steps. -/
theorem eventually_admissible_of_feasibleDirection {n : ℕ} {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) {d : (Fin n → ℝ) × (Fin n → ℝ)}
    (hd : d ∈ feasibleDirections p q) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), AdmissiblePair (p+t • d.1) (q+t • d.2) := by
  have hpq := (admissiblePair_iff p q).mp h
  have he : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ q i+t*d.2 i ∧ q i+t*d.2 i ≤ p i+t*d.1 i ∧ p i+t*d.1 i ≤ 1 := by
    intro i
    have hq := eventually_nonneg_affine (hpq i).1 ((hd.2 i).2.1)
    have hp := eventually_nonneg_affine (sub_nonneg.mpr (hpq i).2.2)
      (b := -d.1 i) (fun hh ↦ neg_nonneg.mpr ((hd.2 i).1 (by linarith)))
    have hg := eventually_nonneg_affine (sub_nonneg.mpr (hpq i).2.1)
      (b := d.1 i-d.2 i) (fun hh ↦ sub_nonneg.mpr ((hd.2 i).2.2 (by linarith)))
    filter_upwards [hq,hp,hg] with t htq htp htg
    exact ⟨htq, by nlinarith, by nlinarith⟩
  have hall := (eventually_all.mpr he)
  filter_upwards [hall] with t ht
  rw [admissiblePair_iff]
  exact ht

/-- The linear gap equation is preserved for every real step. -/
theorem meanGap_add_feasibleDirection {n : ℕ} {p q : Fin n → ℝ}
    {d : (Fin n → ℝ) × (Fin n → ℝ)} (hd : d ∈ feasibleDirections p q) (t : ℝ) :
    meanGap (p+t • d.1) (q+t • d.2) = meanGap p q := by
  simp only [meanGap_eq_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i, p i+t*d.1 i-(q i+t*d.2 i) =
    (p i-q i)+t*(d.1 i-d.2 i) by intro i; ring]
  rw [sum_add_distrib, ← mul_sum, hd.1, mul_zero, add_zero]

/-- Exact feasibility of the rays used by the separation argument. -/
theorem eventually_mem_feasiblePairs_of_direction {n : ℕ} {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) {d : (Fin n → ℝ) × (Fin n → ℝ)}
    (hd : d ∈ feasibleDirections p q) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), (p,q)+t • d ∈ feasiblePairs n (meanGap p q) := by
  filter_upwards [eventually_admissible_of_feasibleDirection h hd] with t ht
  exact ⟨ht, meanGap_add_feasibleDirection hd t⟩

end PoissonBinomialComparison
