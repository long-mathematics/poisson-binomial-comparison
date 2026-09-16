import PoissonBinomialComparison.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Ring

/-!
# Tail sums and the tail objective

The tail-sum identity is proved by finite-set induction using the Bernoulli
insertion recurrence. It is algebraic and needs no bounds on the parameters.

`tailObjective` is the maximum over exactly the thresholds `1, ..., n` when
`n > 0`. At dimension zero only, it is defined to be zero. Nonemptiness proofs
are confined to the definition and its interface, so callers need no typeclass
or proof argument to form the objective. Zero is not inserted into the maximum.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*}

/-- Every coordinate is a Bernoulli parameter. -/
def ValidParameters (p : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ p i ∧ p i ≤ 1

/-- The manuscript's ordered pair of Bernoulli parameter vectors.
The function inequality `q ≤ p` is coordinatewise order. -/
def AdmissiblePair (p q : ι → ℝ) : Prop :=
  ValidParameters p ∧ ValidParameters q ∧ q ≤ p

theorem admissiblePair_iff (p q : ι → ℝ) :
    AdmissiblePair p q ↔ ∀ i, 0 ≤ q i ∧ q i ≤ p i ∧ p i ≤ 1 := by
  constructor
  · rintro ⟨hp, hq, hqp⟩ i
    exact ⟨(hq i).1, hqp i, (hp i).2⟩
  · intro h
    exact ⟨fun i ↦ ⟨(h i).1.trans (h i).2.1, (h i).2.2⟩,
      fun i ↦ ⟨(h i).1, (h i).2.1.trans (h i).2.2⟩, fun i ↦ (h i).2.1⟩

/-- Finite algebraic tail-sum identity on an arbitrary coordinate set. -/
theorem sum_pbTailOn [DecidableEq ι] (p : ι → ℝ) (s : Finset ι) :
    ∑ k ∈ range s.card, pbTailOn p s (k + 1) = ∑ i ∈ s, p i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [card_insert_of_notMem hi, pbTailOn_insert_succ p hi,
      sum_add_distrib, ← mul_sum]
    rw [sum_range_succ (fun k ↦ pbTailOn p s (k + 1)),
      pbTailOn_eq_zero_of_card_lt p (Nat.lt_succ_self s.card), add_zero,
      sum_range_succ' (pbTailOn p s), pbTailOn_zero, ih, sum_insert hi]
    ring

variable {n : ℕ}

/-- The tail-sum identity with thresholds written as successors. -/
theorem sum_pbTail_range (p : Fin n → ℝ) :
    ∑ k ∈ range n, pbTail p (k + 1) = ∑ i, p i := by
  simpa [pbTail] using sum_pbTailOn p univ

/-- The manuscript's identity `∑_{k=1}^n P(S_p ≥ k) = ∑_i p_i`. -/
theorem sum_pbTail (p : Fin n → ℝ) :
    ∑ k ∈ Icc 1 n, pbTail p k = ∑ i, p i := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simpa [Nat.add_comm] using sum_pbTail_range p

theorem sum_tailDiff (p q : Fin n → ℝ) :
    ∑ k ∈ Icc 1 n, tailDiff p q k = meanGap p q := by
  simp only [tailDiff, sum_sub_distrib, sum_pbTail, meanGap]

/-- `T(p,q)`: the exact maximum of `D_k(p,q)` over `1 ≤ k ≤ n`.
Only the empty dimension has the separate value zero. -/
def tailObjective (p q : Fin n → ℝ) : ℝ :=
  if hn : 0 < n then
    (Icc 1 n).sup' (nonempty_Icc.mpr hn) (tailDiff p q)
  else 0

theorem tailObjective_eq_sup' (p q : Fin n → ℝ) (hn : 0 < n) :
    tailObjective p q = (Icc 1 n).sup' (nonempty_Icc.mpr hn) (tailDiff p q) := by
  simp only [tailObjective, dite_eq_left hn]

@[simp] theorem tailObjective_zero (p q : Fin 0 → ℝ) : tailObjective p q = 0 := by
  simp [tailObjective]

/-- Every threshold in the manuscript's range is bounded by the objective. -/
theorem tailDiff_le_tailObjective (p q : Fin n → ℝ) {k : ℕ}
    (hk : k ∈ Icc 1 n) : tailDiff p q k ≤ tailObjective p q := by
  have hn : 0 < n := (mem_Icc.mp hk).1.trans (mem_Icc.mp hk).2
  rw [tailObjective_eq_sup' p q hn]
  exact le_sup' (tailDiff p q) hk

/-- An upper bound on every threshold is an upper bound on the objective. -/
theorem tailObjective_le_iff (p q : Fin n → ℝ) (hn : 0 < n) (a : ℝ) :
    tailObjective p q ≤ a ↔ ∀ k ∈ Icc 1 n, tailDiff p q k ≤ a := by
  rw [tailObjective_eq_sup' p q hn, sup'_le_iff]

/-- A maximizing threshold exists whenever the threshold set is nonempty. -/
theorem tailObjective_attained (p q : Fin n → ℝ) (hn : 0 < n) :
    ∃ k ∈ Icc 1 n, tailObjective p q = tailDiff p q k := by
  rw [tailObjective_eq_sup' p q hn]
  exact exists_mem_eq_sup' (nonempty_Icc.mpr hn) (tailDiff p q)

end

end PoissonBinomialComparison
