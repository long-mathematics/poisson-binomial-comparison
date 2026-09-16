import PoissonBinomialComparison.LikelihoodRatio
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin

/-! # Reindexing finite Bernoulli coordinate sets -/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- Relabeling coordinates by an injection preserves the count law. -/
theorem pbMassIntOn_map (p : κ → ℝ) (e : ι ↪ κ) (s : Finset ι) (k : ℤ) :
    pbMassIntOn p (s.map e) k = pbMassIntOn (fun i ↦ p (e i)) s k := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp
  | @insert i s hi ih =>
    have hei : e i ∉ s.map e := by simpa using hi
    rw [map_insert, pbMassIntOn_insert p hei, pbMassIntOn_insert _ hi, ih, ih]

/-- Relabeling equivalence in the original natural-count representation. -/
theorem pbMassOn_map (p : κ → ℝ) (e : ι ↪ κ) (s : Finset ι) (k : ℕ) :
    pbMassOn p (s.map e) k = pbMassOn (fun i ↦ p (e i)) s k := by
  simpa using pbMassIntOn_map p e s (k : ℤ)

/-- Relabeling coordinates also preserves all finite upper tails. -/
theorem pbTailOn_map (p : κ → ℝ) (e : ι ↪ κ) (s : Finset ι) (k : ℕ) :
    pbTailOn p (s.map e) k = pbTailOn (fun i ↦ p (e i)) s k := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp [pbTailOn, bernoulliWeight]
  | @insert i s hi ih =>
    have hei : e i ∉ s.map e := by simpa using hi
    cases k with
    | zero => simp
    | succ k =>
      rw [map_insert, pbTailOn_insert_succ p hei, pbTailOn_insert_succ _ hi, ih, ih]

/-- Coordinates of a finite parameter set, indexed by its exact cardinality. -/
def finsetParameters (p : ι → ℝ) (s : Finset ι) : Fin s.card → ℝ :=
  fun i ↦ p ((s.equivFin).symm i)

private def finsetEmbedding (s : Finset ι) : Fin s.card ↪ ι :=
  (s.equivFin.symm.toEmbedding).trans ⟨Subtype.val, Subtype.val_injective⟩

omit [DecidableEq ι] in
private theorem map_finsetEmbedding (s : Finset ι) : univ.map (finsetEmbedding s) = s := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    exact (s.equivFin.symm i).property
  · intro hx
    refine mem_map.mpr ⟨s.equivFin ⟨x, hx⟩, mem_univ _, ?_⟩
    simp [finsetEmbedding]

omit [DecidableEq ι] in
/-- Parameter bounds are preserved by finite coordinate enumeration. -/
theorem valid_finsetParameters {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) : ValidParameters (finsetParameters p s) :=
  fun i ↦ hp _ (s.equivFin.symm i).property

/-- Enumerating a finite coordinate set yields the same natural-count mass. -/
theorem pbMass_finsetParameters (p : ι → ℝ) (s : Finset ι) (k : ℕ) :
    pbMass (finsetParameters p s) k = pbMassOn p s k := by
  have h := pbMassOn_map p (finsetEmbedding s) univ k
  rw [map_finsetEmbedding] at h
  exact h.symm

/-- Enumerating a finite coordinate set yields the same upper tail. -/
theorem pbTail_finsetParameters (p : ι → ℝ) (s : Finset ι) (k : ℕ) :
    pbTail (finsetParameters p s) k = pbTailOn p s k := by
  have h := pbTailOn_map p (finsetEmbedding s) univ k
  rw [map_finsetEmbedding] at h
  exact h.symm

omit [DecidableEq ι] in
/-- Enumerating a finite coordinate set preserves the sum of its parameters. -/
theorem sum_finsetParameters (p : ι → ℝ) (s : Finset ι) :
    (∑ i, finsetParameters p s i) = ∑ i ∈ s, p i := by
  have h := sum_map univ (finsetEmbedding s) p
  rw [map_finsetEmbedding] at h
  exact h.symm

variable {n : ℕ}

/-- Prepending a Bernoulli coordinate gives the manuscript's mass recurrence. -/
theorem pbMassInt_cons (p : Fin n → ℝ) (t : ℝ) (k : ℤ) :
    pbMassIntOn (Fin.cons t p) univ k =
      (1 - t) * pbMassIntOn p univ k + t * pbMassIntOn p univ (k - 1) := by
  rw [Fin.univ_succ, cons_eq_insert]
  rw [pbMassIntOn_insert _ (by simp [map_eq_image])]
  rw [pbMassIntOn_map, pbMassIntOn_map]
  rfl

/-- Prepending a Bernoulli coordinate gives the exact positive-threshold recurrence. -/
theorem pbTail_cons (p : Fin n → ℝ) (t : ℝ) (k : ℕ) :
    pbTail (Fin.cons t p) (k + 1) = (1 - t) * pbTail p (k + 1) + t * pbTail p k := by
  unfold pbTail
  rw [Fin.univ_succ, cons_eq_insert]
  rw [pbTailOn_insert_succ _ (by simp [map_eq_image])]
  rw [pbTailOn_map, pbTailOn_map]
  rfl

/-- A common adjoined coordinate forms the convex combination of adjacent differences. -/
theorem tailDiff_cons_common (p q : Fin n → ℝ) (t : ℝ) (k : ℕ) :
    tailDiff (Fin.cons t p) (Fin.cons t q) (k + 1) =
      (1 - t) * tailDiff p q (k + 1) + t * tailDiff p q k := by
  simp only [tailDiff, pbTail_cons]
  ring

/-- A common adjoined coordinate leaves the mean gap unchanged. -/
theorem meanGap_cons_common (p q : Fin n → ℝ) (t : ℝ) :
    meanGap (Fin.cons t p) (Fin.cons t q) = meanGap p q := by
  simp [meanGap, Fin.sum_univ_succ]

end

end PoissonBinomialComparison
