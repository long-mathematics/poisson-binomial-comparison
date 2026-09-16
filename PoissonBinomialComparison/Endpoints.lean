import PoissonBinomialComparison.Tail
import Mathlib.Tactic.Linarith

/-!
# Feasible mean gaps and endpoint cases

The two extreme mean gaps force equality coordinatewise. Deterministic product
laws then give the exact tail objective, without probability-space machinery.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

/-- An ordered admissible pair has nonnegative mean gap. -/
theorem meanGap_nonneg (h : AdmissiblePair p q) : 0 ≤ meanGap p q := by
  rw [meanGap_eq_sum]
  exact sum_nonneg fun i _ ↦ sub_nonneg.mpr (h.2.2 i)

/-- The total gap cannot exceed the number of coordinates. -/
theorem meanGap_le_dimension (h : AdmissiblePair p q) : meanGap p q ≤ n := by
  rw [meanGap_eq_sum]
  calc
    ∑ i, (p i - q i) ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply sum_le_sum
      intro i _
      have hp := (h.1 i).2
      have hq := (h.2.1 i).1
      linarith
    _ = n := by simp

/-- Zero total gap is equivalent to equality of the ordered vectors. -/
theorem meanGap_eq_zero_iff (h : AdmissiblePair p q) :
    meanGap p q = 0 ↔ p = q := by
  constructor
  · intro hz
    rw [meanGap_eq_sum] at hz
    have hall := (sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (univ : Finset (Fin n))) ↦ sub_nonneg.mpr (h.2.2 i))).mp hz
    funext i
    exact sub_eq_zero.mp (hall i (mem_univ i))
  · rintro rfl
    simp [meanGap]

/-- The maximal gap forces every upper coordinate to one and every lower
coordinate to zero, including in dimension zero. -/
theorem meanGap_eq_dimension_iff (h : AdmissiblePair p q) :
    meanGap p q = n ↔ p = (fun _ ↦ 1) ∧ q = (fun _ ↦ 0) := by
  constructor
  · intro hn
    have hz : ∑ i, (1 - (p i - q i)) = (0 : ℝ) := by
      simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      change (n : ℝ) - meanGap p q = 0
      linarith
    have hall := (sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (univ : Finset (Fin n))) ↦ show 0 ≤ 1 - (p i - q i) by
        have hp := (h.1 i).2
        have hq := (h.2.1 i).1
        linarith)).mp hz
    constructor
    · funext i
      have hi := hall i (mem_univ i)
      have hp := (h.1 i).2
      have hq := (h.2.1 i).1
      linarith
    · funext i
      have hi := hall i (mem_univ i)
      have hp := (h.1 i).2
      have hq := (h.2.1 i).1
      linarith
  · rintro ⟨rfl, rfl⟩
    simp [meanGap]

private theorem pbTailOn_const_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) :
    pbTailOn (fun _ ↦ (0 : ℝ)) s k = if k = 0 then 1 else 0 := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    cases k <;> simp [pbTailOn, bernoulliWeight]
  | @insert i s hi ih =>
    cases k with
    | zero => simp
    | succ k => simp [pbTailOn_insert_succ _ hi, ih]

private theorem pbTailOn_const_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) :
    pbTailOn (fun _ ↦ (1 : ℝ)) s k = if k ≤ s.card then 1 else 0 := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    cases k <;> simp [pbTailOn, bernoulliWeight]
  | @insert i s hi ih =>
    cases k with
    | zero => simp
    | succ k => simp [pbTailOn_insert_succ _ hi, ih, card_insert_of_notMem hi]

/-- The all-zero count law is deterministic at zero. -/
theorem pbTail_const_zero (k : ℕ) :
    pbTail (fun _ : Fin n ↦ (0 : ℝ)) k = if k = 0 then 1 else 0 :=
  pbTailOn_const_zero univ k

/-- The all-one count law is deterministic at the dimension. -/
theorem pbTail_const_one (k : ℕ) :
    pbTail (fun _ : Fin n ↦ (1 : ℝ)) k = if k ≤ n then 1 else 0 := by
  simpa [pbTail] using pbTailOn_const_one (univ : Finset (Fin n)) k

/-- Equal parameter vectors have zero tail objective. -/
@[simp] theorem tailObjective_self (p : Fin n → ℝ) : tailObjective p p = 0 := by
  by_cases hn : 0 < n
  · obtain ⟨k, _, hk⟩ := tailObjective_attained p p hn
    simpa [tailDiff] using hk
  · simp [tailObjective, hn]

/-- In positive dimension the two opposite deterministic vectors attain one. -/
theorem tailObjective_const_one_zero (hn : 0 < n) :
    tailObjective (fun _ : Fin n ↦ (1 : ℝ)) (fun _ ↦ 0) = 1 := by
  obtain ⟨k, hk, heq⟩ := tailObjective_attained
    (fun _ : Fin n ↦ (1 : ℝ)) (fun _ ↦ 0) hn
  have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
  simpa [tailDiff, pbTail_const_one, pbTail_const_zero, (mem_Icc.mp hk).2, hk0] using heq

/-- Every admissible zero-gap pair has objective zero. -/
theorem tailObjective_eq_zero_of_meanGap_eq_zero (h : AdmissiblePair p q)
    (hgap : meanGap p q = 0) : tailObjective p q = 0 := by
  rw [(meanGap_eq_zero_iff h).mp hgap]
  exact tailObjective_self q

/-- Every admissible maximal-gap pair has objective one in positive dimension. -/
theorem tailObjective_eq_one_of_meanGap_eq_dimension (h : AdmissiblePair p q)
    (hn : 0 < n) (hgap : meanGap p q = n) : tailObjective p q = 1 := by
  obtain ⟨rfl, rfl⟩ := (meanGap_eq_dimension_iff h).mp hgap
  exact tailObjective_const_one_zero hn

end

end PoissonBinomialComparison
