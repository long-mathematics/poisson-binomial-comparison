import PoissonBinomialComparison.Reindex
import PoissonBinomialComparison.Coordinate
import PoissonBinomialComparison.Endpoints

/-! # Deleting a common coordinate

The remaining parameters are enumerated by `Fin (n-1)`. Deterministic common
coordinates preserve both the mean gap and the exact nonempty tail maximum.
-/

namespace PoissonBinomialComparison

open Finset
open scoped BigOperators

/-- An arbitrary common coordinate can be deleted and the rest relabelled. -/
theorem exists_deleted_common_pair {n : ℕ} {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (i : Fin n) (heq : p i = q i) :
    ∃ r s : Fin (n - 1) → ℝ, AdmissiblePair r s ∧ meanGap r s = meanGap p q ∧
      ∀ k, tailDiff p q (k + 1) =
        (1 - p i) * tailDiff r s (k + 1) + p i * tailDiff r s k := by
  let u := (univ.erase i : Finset (Fin n))
  have hcard : u.card = n - 1 := by simp [u]
  have hex : ∃ r s : Fin u.card → ℝ, AdmissiblePair r s ∧
      meanGap r s = meanGap p q ∧ ∀ k, tailDiff p q (k + 1) =
        (1 - p i) * tailDiff r s (k + 1) + p i * tailDiff r s k := by
    refine ⟨finsetParameters p u, finsetParameters q u, ?_, ?_, ?_⟩
    · exact ⟨valid_finsetParameters _ (fun j _ => h.1 j),
        valid_finsetParameters _ (fun j _ => h.2.1 j), fun j => h.2.2 _⟩
    · simp only [meanGap, sum_finsetParameters]
      have hp := sum_erase_add univ p (mem_univ i)
      have hq := sum_erase_add univ q (mem_univ i)
      dsimp [u]
      linarith
    · intro k
      simp only [tailDiff, pbTail_finsetParameters]
      rw [pbTail_delete_succ p i, pbTail_delete_succ q i, ← heq]
      dsimp [u]
      ring
  rwa [hcard] at hex

/-- Removing a shared deterministic coordinate preserves the maximum exactly. -/
theorem exists_deleted_deterministic_pair {n : ℕ} (hn : 2 ≤ n) {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (i : Fin n) (heq : p i = q i)
    (hdet : p i = 0 ∨ p i = 1) :
    ∃ r s : Fin (n - 1) → ℝ, AdmissiblePair r s ∧ meanGap r s = meanGap p q ∧
      tailObjective r s = tailObjective p q := by
  obtain ⟨r,s,hrs,hgap,hrec⟩ := exists_deleted_common_pair h i heq
  refine ⟨r,s,hrs,hgap,le_antisymm ?_ ?_⟩
  · obtain ⟨k,hk,hmax⟩ := tailObjective_attained r s (by omega)
    rcases hdet with hz | ho
    · have he := hrec (k-1)
      have hk1 : k - 1 + 1 = k := by have := (mem_Icc.mp hk).1; omega
      simp only [hz, sub_zero, one_mul, zero_mul, add_zero, hk1] at he
      rw [hmax, ← he]
      exact tailDiff_le_tailObjective p q (mem_Icc.mpr ⟨(mem_Icc.mp hk).1, by have := (mem_Icc.mp hk).2; omega⟩)
    · have he := hrec k
      simp only [ho, sub_self, zero_mul, one_mul, zero_add] at he
      rw [hmax, ← he]
      exact tailDiff_le_tailObjective p q (mem_Icc.mpr ⟨by omega, by have := (mem_Icc.mp hk).2; omega⟩)
  · apply (tailObjective_le_iff p q (by omega) _).mpr
    intro k hk
    have hk0 := (mem_Icc.mp hk).1
    have hkn := (mem_Icc.mp hk).2
    have he := hrec (k-1)
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1] at he
    rcases hdet with hz | ho
    · simp only [hz, sub_zero, one_mul, zero_mul, add_zero] at he
      rw [he]
      by_cases hkm : k ≤ n-1
      · exact tailDiff_le_tailObjective r s (mem_Icc.mpr ⟨hk0,hkm⟩)
      · have hz' : tailDiff r s k = 0 := by
          simp [tailDiff, pbTail_eq_zero_of_lt r (by omega : n-1 < k),
            pbTail_eq_zero_of_lt s (by omega : n-1 < k)]
        rw [hz']
        exact (tailDiff_nonneg hrs 1).trans (tailDiff_le_tailObjective r s (by simp; omega))
    · simp only [ho, sub_self, zero_mul, one_mul, zero_add] at he
      rw [he]
      by_cases hk2 : 1 ≤ k-1
      · exact tailDiff_le_tailObjective r s (mem_Icc.mpr ⟨hk2, by omega⟩)
      · have hkz : k-1 = 0 := by omega
        simp only [hkz, tailDiff, pbTail_zero, sub_self]
        exact (tailDiff_nonneg hrs 1).trans (tailDiff_le_tailObjective r s (by simp; omega))

end PoissonBinomialComparison
