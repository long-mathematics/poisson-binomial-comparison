import PoissonBinomialComparison.Tail
import Mathlib.Tactic.Linarith

/-!
# Reflection of the Bernoulli comparison

Complementing successful-coordinate subsets proves the count-law reflection
algebraically. Reflecting an ordered pair exchanges and complements its vectors,
which preserves the mean gap and reverses the finite range of tail thresholds.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ}

/-- Complementing every Bernoulli parameter complements the outcome subset. -/
theorem bernoulliWeight_complement (p : Fin n → ℝ) (A : Finset (Fin n)) :
    bernoulliWeight (fun i ↦ 1 - p i) univ A = bernoulliWeight p univ Aᶜ := by
  simp [bernoulliWeight, compl_eq_univ_sdiff, mul_comm]

private theorem sum_powerset_complement (f : Finset (Fin n) → ℝ) :
    ∑ A ∈ (univ : Finset (Fin n)).powerset, f A =
      ∑ A ∈ (univ : Finset (Fin n)).powerset, f Aᶜ := by
  apply sum_nbij' (fun A ↦ Aᶜ) (fun A ↦ Aᶜ)
  · intro A _; simp
  · intro A _; simp
  · intro A _; simp
  · intro A _; simp
  · intro A _; simp

/-- Reflection reverses the count masses on their support. -/
theorem pbMass_complement (p : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    pbMass (fun i ↦ 1 - p i) k = pbMass p (n - k) := by
  simp only [pbMass, pbMassOn_eq_sum_powerset]
  rw [sum_powerset_complement]
  simp only [bernoulliWeight_complement, compl_compl]
  apply sum_congr rfl
  intro A _
  have hcard : A.card ≤ n := by simpa using card_le_univ A
  simp only [card_compl, Fintype.card_fin]
  have heq : n - A.card = k ↔ A.card = n - k := by omega
  simp only [heq]

/-- Reflection of upper tails, including thresholds zero and `n + 1`.
The expression `n + 1 - k` avoids truncated-subtraction ambiguity. -/
theorem pbTail_complement (p : Fin n → ℝ) (k : ℕ) (hk : k ≤ n + 1) :
    pbTail (fun i ↦ 1 - p i) k = 1 - pbTail p (n + 1 - k) := by
  unfold pbTail pbTailOn
  rw [sum_powerset_complement]
  simp only [bernoulliWeight_complement, compl_compl]
  rw [← sum_bernoulliWeight p (univ : Finset (Fin n)), ← sum_sub_distrib]
  apply sum_congr rfl
  intro A _
  have hcard : A.card ≤ n := by simpa using card_le_univ A
  simp only [card_compl, Fintype.card_fin]
  by_cases h : n + 1 - k ≤ A.card
  · have hh : ¬ k ≤ n - A.card := by omega
    simp [h, hh]
  · have hh : k ≤ n - A.card := by omega
    simp [h, hh]

/-- Reflection preserves the total mean gap. -/
theorem meanGap_reflection (p q : Fin n → ℝ) :
    meanGap (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) = meanGap p q := by
  simp only [meanGap, sum_sub_distrib]
  ring

/-- Reflection preserves the manuscript's feasibility assumptions. -/
theorem admissiblePair_reflection {p q : Fin n → ℝ} (h : AdmissiblePair p q) :
    AdmissiblePair (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) := by
  rw [admissiblePair_iff] at h ⊢
  intro i
  obtain ⟨hq, hqp, hp⟩ := h i
  exact ⟨sub_nonneg.mpr hp, sub_le_sub_left hqp 1, by linarith⟩

/-- Reflection sends threshold `k` to `n + 1 - k`. -/
theorem tailDiff_reflection (p q : Fin n → ℝ) (k : ℕ) (hk : k ≤ n + 1) :
    tailDiff (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) k =
      tailDiff p q (n + 1 - k) := by
  simp only [tailDiff, pbTail_complement _ k hk]
  ring

/-- The manuscript's `n - k + 1` notation agrees with reflected thresholds
on its threshold range. -/
theorem tailDiff_reflection_of_mem (p q : Fin n → ℝ) {k : ℕ}
    (hk : k ∈ Icc 1 n) :
    tailDiff (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) k =
      tailDiff p q (n - k + 1) := by
  have hkn := (mem_Icc.mp hk).2
  rw [tailDiff_reflection p q k (by omega)]
  congr 1
  omega

private theorem tailObjective_reflection_le (p q : Fin n → ℝ) (hn : 0 < n) :
    tailObjective (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) ≤ tailObjective p q := by
  rw [tailObjective_le_iff _ _ hn]
  intro k hk
  have hkr := mem_Icc.mp hk
  rw [tailDiff_reflection p q k (by omega)]
  exact tailDiff_le_tailObjective p q (mem_Icc.mpr (by omega))

/-- Reflection preserves the finite maximum, including the dimension-zero convention. -/
theorem tailObjective_reflection (p q : Fin n → ℝ) :
    tailObjective (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) = tailObjective p q := by
  by_cases hn : 0 < n
  · apply le_antisymm (tailObjective_reflection_le p q hn)
    simpa only [sub_sub_cancel] using
      tailObjective_reflection_le (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) hn
  · simp [tailObjective, hn]

end

end PoissonBinomialComparison
