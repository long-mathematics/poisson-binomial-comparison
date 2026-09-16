import PoissonBinomialComparison.TwoDimensional

/-!
# Finite product total variation

Product Bernoulli outcomes are the same successful-coordinate subsets used in
`Basic`. The half sum of absolute signed outcome weights is the manuscript's
finite total variation formula. Event bounds below are algebraic: normalization
alone suffices, even without nonnegativity of the individual outcome weights.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

/-- Product total variation in the manuscript's finite-outcome convention. -/
def productTV {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  (∑ A ∈ (univ : Finset (Fin n)).powerset,
    |bernoulliWeight p univ A - bernoulliWeight q univ A|) / 2

private theorem sum_event_le_half_sum_abs {α : Type*} (s : Finset α)
    (f : α → ℝ) (P : α → Prop) [DecidablePred P] (hf : ∑ x ∈ s, f x = 0) :
    (∑ x ∈ s, if P x then f x else 0) ≤ (∑ x ∈ s, |f x|) / 2 := by
  have h : (∑ x ∈ s, (2 * (if P x then f x else 0) - f x)) ≤
      ∑ x ∈ s, |f x| := by
    apply sum_le_sum
    intro x hx
    by_cases hP : P x
    · simp only [ite_eq_left hP]
      linarith [le_abs_self (f x)]
    · simp only [ite_eq_right hP, mul_zero, zero_sub]
      exact neg_le_abs (f x)
  rw [sum_sub_distrib, ← mul_sum, hf, sub_zero] at h
  linarith

theorem productTV_nonneg {n : ℕ} (p q : Fin n → ℝ) : 0 ≤ productTV p q := by
  exact div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)

@[simp] theorem productTV_self {n : ℕ} (p : Fin n → ℝ) : productTV p p = 0 := by
  simp [productTV]

/-- Every event difference is bounded by product total variation. -/
theorem eventDiff_le_productTV {n : ℕ} (p q : Fin n → ℝ)
    (P : Finset (Fin n) → Prop) [DecidablePred P] :
    (∑ A ∈ (univ : Finset (Fin n)).powerset,
      if P A then bernoulliWeight p univ A - bernoulliWeight q univ A else 0) ≤
        productTV p q := by
  apply sum_event_le_half_sum_abs
  rw [sum_sub_distrib, sum_bernoulliWeight, sum_bernoulliWeight, sub_self]

theorem tailDiff_le_productTV {n : ℕ} (p q : Fin n → ℝ) (k : ℕ) :
    tailDiff p q k ≤ productTV p q := by
  have h := eventDiff_le_productTV p q (fun A ↦ k ≤ A.card)
  convert h using 1
  simp only [tailDiff, pbTail, pbTailOn, ← sum_sub_distrib]
  apply sum_congr rfl
  intro A hA
  split_ifs <;> simp

theorem tailObjective_le_productTV {n : ℕ} (p q : Fin n → ℝ) :
    tailObjective p q ≤ productTV p q := by
  cases n with
  | zero => simpa using productTV_nonneg p q
  | succ n =>
    exact (tailObjective_le_iff p q (Nat.succ_pos n) _).mpr
      fun k _ ↦ tailDiff_le_productTV p q k

end

end PoissonBinomialComparison
