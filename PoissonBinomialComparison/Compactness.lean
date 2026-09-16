import PoissonBinomialComparison.Endpoints
import PoissonBinomialComparison.Homogeneous
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice

/-!
# Continuity and existence of fixed-gap minimizers

The finite subset formulas are continuous polynomials in the parameters. The
exact finite maximum is continuous, and the admissible fixed-gap set is compact.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

@[fun_prop] theorem continuous_bernoulliWeight (s A : Finset ι) :
    Continuous (fun p : ι → ℝ ↦ bernoulliWeight p s A) := by
  unfold bernoulliWeight
  fun_prop

@[fun_prop] theorem continuous_pbMassOn (s : Finset ι) (k : ℕ) :
    Continuous (fun p : ι → ℝ ↦ pbMassOn p s k) := by
  unfold pbMassOn
  fun_prop

@[fun_prop] theorem continuous_pbTailOn (s : Finset ι) (k : ℕ) :
    Continuous (fun p : ι → ℝ ↦ pbTailOn p s k) := by
  unfold pbTailOn
  apply continuous_finsetSum
  intro A _
  split_ifs <;> fun_prop

variable {n : ℕ}

@[fun_prop] theorem continuous_pbMass (k : ℕ) :
    Continuous (fun p : Fin n → ℝ ↦ pbMass p k) := continuous_pbMassOn univ k

@[fun_prop] theorem continuous_pbTail (k : ℕ) :
    Continuous (fun p : Fin n → ℝ ↦ pbTail p k) := continuous_pbTailOn univ k

@[fun_prop] theorem continuous_meanGap :
    Continuous (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ meanGap x.1 x.2) := by
  unfold meanGap
  fun_prop

@[fun_prop] theorem continuous_tailDiff (k : ℕ) :
    Continuous (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailDiff x.1 x.2 k) := by
  unfold tailDiff
  fun_prop

@[fun_prop] theorem continuous_tailObjective :
    Continuous (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2) := by
  by_cases hn : 0 < n
  · simp only [tailObjective, dite_eq_left hn]
    exact Continuous.finset_sup'_apply _ (fun k _ ↦ continuous_tailDiff k)
  · simp only [tailObjective, dite_eq_right hn]
    exact continuous_const

/-- The manuscript's ordered parameter set at a prescribed mean gap. -/
def feasiblePairs (n : ℕ) (Δ : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {x | AdmissiblePair x.1 x.2 ∧ meanGap x.1 x.2 = Δ}

theorem isClosed_admissiblePairs :
    IsClosed {x : (Fin n → ℝ) × (Fin n → ℝ) | AdmissiblePair x.1 x.2} := by
  have hc : ∀ i : Fin n, IsClosed {x : (Fin n → ℝ) × (Fin n → ℝ) |
      0 ≤ x.2 i ∧ x.2 i ≤ x.1 i ∧ x.1 i ≤ 1} := by
    intro i
    have hp : Continuous (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ x.1 i) := by fun_prop
    have hq : Continuous (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ x.2 i) := by fun_prop
    exact (isClosed_le continuous_const hq).inter
      ((isClosed_le hq hp).inter (isClosed_le hp continuous_const))
  convert isClosed_iInter hc using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  exact admissiblePair_iff x.1 x.2

theorem isClosed_feasiblePairs (Δ : ℝ) : IsClosed (feasiblePairs n Δ) :=
  isClosed_admissiblePairs.inter (isClosed_eq continuous_meanGap continuous_const)

theorem isCompact_feasiblePairs (Δ : ℝ) : IsCompact (feasiblePairs n Δ) := by
  apply (isCompact_Icc : IsCompact (Set.Icc
    ((0 : Fin n → ℝ), (0 : Fin n → ℝ)) (1, 1))).of_isClosed_subset
      (isClosed_feasiblePairs Δ)
  intro x hx
  exact ⟨⟨fun i ↦ (hx.1.1 i).1, fun i ↦ (hx.1.2.1 i).1⟩,
    ⟨fun i ↦ (hx.1.1 i).2, fun i ↦ (hx.1.2.1 i).2⟩⟩

/-- Every feasible fixed-gap set has a minimizing pair. -/
theorem exists_tailObjective_minimizer_of_nonempty (Δ : ℝ)
    (hne : (feasiblePairs n Δ).Nonempty) :
    ∃ p q : Fin n → ℝ, AdmissiblePair p q ∧ meanGap p q = Δ ∧
      ∀ p' q' : Fin n → ℝ, AdmissiblePair p' q' → meanGap p' q' = Δ →
        tailObjective p q ≤ tailObjective p' q' := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_feasiblePairs (n := n) Δ).exists_isMinOn
    (f := fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2)
    hne (continuous_tailObjective (n := n)).continuousOn
  refine ⟨x.1, x.2, hx.1, hx.2, ?_⟩
  intro p q hp hgap
  exact (isMinOn_iff.mp hmin) (p, q) ⟨hp, hgap⟩

/-- Every gap in the manuscript's closed feasible range is realized. -/
theorem feasiblePairs_nonempty (Δ : ℝ) (h0 : 0 ≤ Δ) (hn : Δ ≤ n) :
    (feasiblePairs n Δ).Nonempty := by
  by_cases hnp : 0 < n
  · have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
    refine ⟨((fun _ ↦ Δ / n), (fun _ ↦ 0)), ?_, ?_⟩
    · rw [admissiblePair_iff]
      intro i
      exact ⟨le_rfl, div_nonneg h0 hnr.le, (div_le_one hnr).mpr hn⟩
    · rw [meanGap_const]
      rw [sub_zero, mul_div_cancel₀ _ hnr.ne']
  · have hn0 : n = 0 := by omega
    have hΔ : Δ = 0 := by simp [hn0] at hn; linarith
    refine ⟨((fun _ ↦ 0), (fun _ ↦ 0)), ?_, ?_⟩
    · rw [admissiblePair_iff]
      intro i
      norm_num
    · simp [meanGap, hΔ]

/-- Compactness supplies the fixed-gap global minimizer used in the induction,
including both endpoint gaps and dimension zero. -/
theorem exists_tailObjective_minimizer (Δ : ℝ) (h0 : 0 ≤ Δ) (hn : Δ ≤ n) :
    ∃ p q : Fin n → ℝ, AdmissiblePair p q ∧ meanGap p q = Δ ∧
      ∀ p' q' : Fin n → ℝ, AdmissiblePair p' q' → meanGap p' q' = Δ →
        tailObjective p q ≤ tailObjective p' q' :=
  exists_tailObjective_minimizer_of_nonempty Δ (feasiblePairs_nonempty Δ h0 hn)

end

end PoissonBinomialComparison
