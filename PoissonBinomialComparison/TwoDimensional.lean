import PoissonBinomialComparison.Tail
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# The two-dimensional minimum value

The base case uses `D₁ + D₂ = Δ`, so the maximum of the two differences is at
least `Δ / 2`. This lower bound is algebraic and holds even without parameter
bounds or coordinatewise order. For every `0 ≤ Δ ≤ 2`, the manuscript's
complementary homogeneous pair is admissible, has mean gap `Δ`, and attains
the lower bound. No classification of the other equality cases is made.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

/-- The manuscript's base-case identity `D₁ + D₂ = Δ`. -/
theorem tailDiff_one_add_two (p q : Fin 2 → ℝ) :
    tailDiff p q 1 + tailDiff p q 2 = meanGap p q := by
  have h : Icc (1 : ℕ) 2 = {1, 2} := by decide
  simpa [h] using sum_tailDiff p q

/-- In two dimensions the objective is exactly the maximum of the two tails. -/
theorem tailObjective_two (p q : Fin 2 → ℝ) :
    tailObjective p q = max (tailDiff p q 1) (tailDiff p q 2) := by
  rw [tailObjective_eq_sup' p q (by decide)]
  have h : Icc (1 : ℕ) 2 = {1, 2} := by decide
  simp [h, sup'_insert (singleton_nonempty 2)]

/-- The uppermost two-dimensional tail is the product of the parameters. -/
theorem pbTail_two_two (p : Fin 2 → ℝ) : pbTail p 2 = p 0 * p 1 := by
  rw [pbTail_eq_sum_mass, Icc_self, sum_singleton, pbMass, pbMassOn]
  have h : (univ : Finset (Fin 2)).powersetCard 2 = {univ} := by
    simpa using powersetCard_self (univ : Finset (Fin 2))
  rw [h]
  simp [bernoulliWeight, Fin.prod_univ_two]

/-- The `n = 2` lower bound. It holds for all real vectors, hence in particular
for the manuscript's admissible pairs. -/
theorem twoDimensional_lower_bound (p q : Fin 2 → ℝ) :
    meanGap p q / 2 ≤ tailObjective p q := by
  have hsum := tailDiff_one_add_two p q
  have h1 := tailDiff_le_tailObjective p q (k := 1) (by decide)
  have h2 := tailDiff_le_tailObjective p q (k := 2) (by decide)
  linarith

/-- The manuscript's complementary homogeneous pair is feasible at gap `Δ`
and attains the exact lower bound, including both endpoint gaps. -/
theorem complementaryPair_two_attains (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ2 : Δ ≤ 2) :
    let p : Fin 2 → ℝ := fun _ ↦ (1 + Δ / 2) / 2
    let q : Fin 2 → ℝ := fun _ ↦ (1 - Δ / 2) / 2
    AdmissiblePair p q ∧ meanGap p q = Δ ∧ tailObjective p q = Δ / 2 := by
  let p : Fin 2 → ℝ := fun _ ↦ (1 + Δ / 2) / 2
  let q : Fin 2 → ℝ := fun _ ↦ (1 - Δ / 2) / 2
  change AdmissiblePair p q ∧ meanGap p q = Δ ∧ tailObjective p q = Δ / 2
  have hgap : meanGap p q = Δ := by
    simp only [meanGap, Fin.sum_univ_two, p, q]
    ring
  have htwo : tailDiff p q 2 = Δ / 2 := by
    rw [tailDiff, pbTail_two_two, pbTail_two_two]
    dsimp [p, q]
    ring
  have hone : tailDiff p q 1 = Δ / 2 := by
    have hsum := tailDiff_one_add_two p q
    rw [hgap, htwo] at hsum
    linarith
  refine ⟨?_, hgap, ?_⟩
  · rw [admissiblePair_iff]
    intro i
    dsimp [p, q]
    constructor
    · linarith
    · constructor <;> linarith
  · rw [tailObjective_two, hone, htwo, max_self]

end

end PoissonBinomialComparison
