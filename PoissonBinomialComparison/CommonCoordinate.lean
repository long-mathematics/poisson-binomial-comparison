import PoissonBinomialComparison.Reindex
import PoissonBinomialComparison.TotalVariationHomogeneous

/-! # Common-coordinate adjoining and deterministic deletion -/

namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

/-- Prepending an admissible pair of coordinates preserves admissibility. -/
theorem admissiblePair_cons (h : AdmissiblePair p q) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    AdmissiblePair (Fin.cons a p) (Fin.cons b q) := by
  rw [admissiblePair_iff]
  exact Fin.cases ⟨hb, hba, ha⟩ (fun i ↦ (admissiblePair_iff p q).mp h i)

/-- For admissible pairs the zero and out-of-support tail differences are also
bounded by the exact objective. This does not change its maximum definition. -/
theorem tailDiff_le_tailObjective_all (h : AdmissiblePair p q) (k : ℕ) :
    tailDiff p q k ≤ tailObjective p q := by
  by_cases hk : k ∈ Icc 1 n
  · exact tailDiff_le_tailObjective p q hk
  by_cases hk0 : k = 0
  · simpa [hk0, tailDiff] using tailObjective_nonneg h
  · have hkn : n < k := by simp only [mem_Icc] at hk; omega
    simpa [tailDiff, pbTail_eq_zero_of_lt p hkn, pbTail_eq_zero_of_lt q hkn] using
      tailObjective_nonneg h

/-- Adjoining the same Bernoulli parameter can only decrease the tail objective. -/
theorem tailObjective_cons_common_le (h : AdmissiblePair p q) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) :
    tailObjective (Fin.cons t p) (Fin.cons t q) ≤ tailObjective p q := by
  rw [tailObjective_le_iff _ _ (Nat.succ_pos n)]
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := (mem_Icc.mp hk).1; omega : k ≠ 0)
  rw [tailDiff_cons_common]
  have h0 := mul_nonneg (sub_nonneg.mpr ht.2)
    (sub_nonneg.mpr (tailDiff_le_tailObjective_all h (j + 1)))
  have h1 := mul_nonneg ht.1 (sub_nonneg.mpr (tailDiff_le_tailObjective_all h j))
  nlinarith

/-- Adjoining a common deterministic zero preserves the exact objective. -/
theorem tailObjective_cons_zero (h : AdmissiblePair p q) :
    tailObjective (Fin.cons 0 p) (Fin.cons 0 q) = tailObjective p q := by
  apply le_antisymm (tailObjective_cons_common_le h ⟨le_rfl, zero_le_one⟩)
  by_cases hn : 0 < n
  · obtain ⟨k, hk, heq⟩ := tailObjective_attained p q hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := (mem_Icc.mp hk).1; omega : k ≠ 0)
    have hk' : j + 1 ∈ Icc 1 (n + 1) := by simp only [mem_Icc] at hk ⊢; omega
    have hb := tailDiff_le_tailObjective (Fin.cons 0 p) (Fin.cons 0 q) hk'
    simpa [tailDiff_cons_common, heq] using hb
  · have hn0 : n = 0 := by omega
    subst n
    simpa using tailObjective_nonneg (admissiblePair_cons h le_rfl le_rfl zero_le_one)

/-- Adjoining a common deterministic one shifts thresholds and preserves the objective. -/
theorem tailObjective_cons_one (h : AdmissiblePair p q) :
    tailObjective (Fin.cons 1 p) (Fin.cons 1 q) = tailObjective p q := by
  apply le_antisymm (tailObjective_cons_common_le h ⟨zero_le_one, le_rfl⟩)
  by_cases hn : 0 < n
  · obtain ⟨k, hk, heq⟩ := tailObjective_attained p q hn
    have hk' : k + 1 ∈ Icc 1 (n + 1) := by simp only [mem_Icc] at hk ⊢; omega
    have hb := tailDiff_le_tailObjective (Fin.cons 1 p) (Fin.cons 1 q) hk'
    simpa [tailDiff_cons_common, heq] using hb
  · have hn0 : n = 0 := by omega
    subst n
    simpa using tailObjective_nonneg (admissiblePair_cons h zero_le_one le_rfl le_rfl)

end

end PoissonBinomialComparison
