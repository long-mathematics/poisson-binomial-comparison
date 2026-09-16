import PoissonBinomialComparison.ActiveThresholds
import PoissonBinomialComparison.TotalVariation
import PoissonBinomialComparison.Homogeneous

/-!
# Total variation for homogeneous product Bernoulli laws

Likelihood-ratio order makes the positive count-mass differences an upper tail.
For homogeneous product laws, each count fiber has a common signed outcome
weight, so grouping by count preserves total variation exactly.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

/-- Total variation of the count distributions, in finite half-sum convention. -/
def countTV (p q : Fin n → ℝ) : ℝ :=
  (∑ k ∈ range (n + 1), |pbMass p k - pbMass q k|) / 2

theorem countTV_nonneg (p q : Fin n → ℝ) : 0 ≤ countTV p q :=
  div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)

@[simp] theorem countTV_self (p : Fin n → ℝ) : countTV p p = 0 := by
  simp [countTV]

/-- Normalization makes the total signed count mass zero. -/
theorem sum_massDiff (p q : Fin n → ℝ) :
    ∑ k ∈ range (n + 1), (pbMass p k - pbMass q k) = 0 := by
  rw [sum_sub_distrib, sum_pbMass, sum_pbMass, sub_self]

/-- A positive count-mass difference cannot be followed by a negative one. -/
theorem massDiff_nonneg_after_pos (h : AdmissiblePair p q) {i j : ℕ}
    (hij : i ≤ j) (hi : pbMass q i < pbMass p i) : pbMass q j ≤ pbMass p j := by
  by_contra hnot
  have hj : pbMass p j < pbMass q j := lt_of_not_ge hnot
  have hqj : 0 < pbMass q j := (pbMass_nonneg h.1 j).trans_lt hj
  have hstrict := mul_lt_mul_of_pos_right hi hqj
  have hweak := mul_le_mul_of_nonneg_left hj.le (pbMass_nonneg h.2.1 i)
  have hlr := pbMass_likelihoodRatio h i j hij
  nlinarith

/-- At zero successes, coordinatewise increasing parameters cannot increase mass. -/
theorem pbMass_zero_antitone (h : AdmissiblePair p q) : pbMass p 0 ≤ pbMass q 0 := by
  have hd := tailDiff_sub_succ p q 0
  have hn := tailDiff_nonneg h 1
  simp only [tailDiff, pbTail_zero, sub_self, zero_add, zero_sub] at hd
  change 0 ≤ pbTail p 1 - pbTail q 1 at hn
  linarith

/-- The tail difference as a count-range sum with a threshold indicator. -/
theorem tailDiff_eq_sum_count_indicator (p q : Fin n → ℝ) (k : ℕ) :
    tailDiff p q k = ∑ j ∈ range (n + 1),
      if k ≤ j then pbMass p j - pbMass q j else 0 := by
  rw [← sum_filter]
  have heq : (range (n + 1)).filter (fun j ↦ k ≤ j) = Icc k n := by
    ext j
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  rw [heq]
  exact tailDiff_eq_sum_mass p q k

/-- If count-mass signs change at a threshold, that tail difference is the full
count total variation. -/
theorem countTV_eq_tailDiff_of_signs (p q : Fin n → ℝ) (k : ℕ)
    (hbefore : ∀ j < k, pbMass p j ≤ pbMass q j)
    (hafter : ∀ j, k ≤ j → pbMass q j ≤ pbMass p j) :
    countTV p q = tailDiff p q k := by
  have habs : ∑ j ∈ range (n + 1), |pbMass p j - pbMass q j| =
      ∑ j ∈ range (n + 1),
        (2 * (if k ≤ j then pbMass p j - pbMass q j else 0) -
          (pbMass p j - pbMass q j)) := by
    apply sum_congr rfl
    intro j _
    by_cases hj : k ≤ j
    · rw [ite_eq_left hj, abs_of_nonneg (sub_nonneg.mpr (hafter j hj))]
      ring
    · rw [ite_eq_right hj, abs_of_nonpos (sub_nonpos.mpr (hbefore j (by omega)))]
      ring
  rw [sum_sub_distrib, ← mul_sum, sum_massDiff, sub_zero,
    ← tailDiff_eq_sum_count_indicator] at habs
  unfold countTV
  rw [habs]
  ring

/-- The tail objective of an admissible pair is nonnegative, even in dimension zero. -/
theorem tailObjective_nonneg (h : AdmissiblePair p q) : 0 ≤ tailObjective p q := by
  cases n with
  | zero => simp
  | succ n =>
    obtain ⟨k, _, hk⟩ := tailObjective_attained p q (by omega)
    rw [hk]
    exact tailDiff_nonneg h k

/-- Count total variation equals the maximum tail difference for every ordered
Bernoulli parameter pair, including all degenerate cases. -/
theorem countTV_eq_tailObjective (h : AdmissiblePair p q) :
    countTV p q = tailObjective p q := by
  let pos := (range (n + 1)).filter (fun k ↦ pbMass q k < pbMass p k)
  by_cases hpos : pos.Nonempty
  · let k := pos.min' hpos
    have hk : k ∈ pos := min'_mem _ hpos
    have hkm := mem_filter.mp hk
    have hk1 : 1 ≤ k := by
      have hz := pbMass_zero_antitone h
      by_contra hnot
      have heq : k = 0 := by omega
      rw [heq] at hkm
      exact not_lt_of_ge hz hkm.2
    have hkn : k ≤ n := by have := mem_range.mp hkm.1; omega
    have hbefore : ∀ j < k, pbMass p j ≤ pbMass q j := by
      intro j hj
      by_contra hnot
      have hjmem : j ∈ pos := mem_filter.mpr ⟨mem_range.mpr (by omega), lt_of_not_ge hnot⟩
      have hmin : k ≤ j := min'_le _ j hjmem
      omega
    have hafter : ∀ j, k ≤ j → pbMass q j ≤ pbMass p j :=
      fun j hj ↦ massDiff_nonneg_after_pos h hj hkm.2
    rw [countTV_eq_tailDiff_of_signs p q k hbefore hafter]
    apply le_antisymm (tailDiff_le_tailObjective p q (mem_Icc.mpr ⟨hk1, hkn⟩))
    rw [tailObjective_le_iff p q (by omega)]
    intro l _
    rw [tailDiff_eq_sum_count_indicator p q l, tailDiff_eq_sum_count_indicator p q k]
    apply sum_le_sum
    intro j _
    by_cases hjl : l ≤ j <;> by_cases hjk : k ≤ j
    · simp only [hjl, hjk, ite_true, le_refl]
    · simp only [hjl, hjk, ite_true, ite_false]
      exact sub_nonpos.mpr (hbefore j (by omega))
    · simp only [hjl, hjk, ite_false, ite_true]
      exact sub_nonneg.mpr (hafter j hjk)
    · simp only [hjl, hjk, ite_false, le_refl]
  · have hnonpos : ∀ j, pbMass p j ≤ pbMass q j := by
      intro j
      by_cases hj : j ≤ n
      · by_contra hnot
        exact hpos ⟨j, mem_filter.mpr ⟨mem_range.mpr (by omega), lt_of_not_ge hnot⟩⟩
      · rw [pbMass_eq_zero_of_lt p (by omega), pbMass_eq_zero_of_lt q (by omega)]
    have hcount : countTV p q = 0 := by
      unfold countTV
      simp_rw [abs_of_nonpos (sub_nonpos.mpr (hnonpos _))]
      rw [sum_neg_distrib, sum_massDiff]
      norm_num
    rw [hcount]
    apply le_antisymm (tailObjective_nonneg h)
    cases n with
    | zero => simp
    | succ n =>
      rw [tailObjective_le_iff p q (by omega)]
      intro k _
      rw [tailDiff_eq_sum_mass]
      exact sum_nonpos fun j _ ↦ sub_nonpos.mpr (hnonpos j)

/-- Homogeneous product-law total variation is unchanged by grouping outcomes
by count. This identity is algebraic and holds for arbitrary real parameters. -/
theorem productTV_const_eq_countTV (n : ℕ) (a b : ℝ) :
    productTV (fun _ : Fin n ↦ a) (fun _ ↦ b) =
      countTV (fun _ : Fin n ↦ a) (fun _ ↦ b) := by
  unfold productTV countTV
  congr 1
  rw [sum_powerset]
  simp only [card_univ, Fintype.card_fin]
  apply sum_congr rfl
  intro k _
  calc
    (∑ A ∈ (univ : Finset (Fin n)).powersetCard k,
        |bernoulliWeight (fun _ ↦ a) univ A - bernoulliWeight (fun _ ↦ b) univ A|) =
        ∑ _A ∈ (univ : Finset (Fin n)).powersetCard k,
          |a ^ k * (1 - a) ^ (n - k) - b ^ k * (1 - b) ^ (n - k)| := by
      apply sum_congr rfl
      intro A hA
      rw [bernoulliWeight_const a (mem_powersetCard.mp hA).1,
        bernoulliWeight_const b (mem_powersetCard.mp hA).1, (mem_powersetCard.mp hA).2]
      simp only [card_univ, Fintype.card_fin]
    _ = |pbMass (fun _ : Fin n ↦ a) k - pbMass (fun _ : Fin n ↦ b) k| := by
      simp only [sum_const, nsmul_eq_mul, card_powersetCard, card_univ, Fintype.card_fin,
        pbMass_const, mul_assoc]
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose k) : (0 : ℝ) ≤ _)]

/-- For homogeneous ordered Bernoulli product laws, total variation is exactly
the manuscript's count-tail objective. Dimension zero, equal parameters, and
deterministic endpoints are included. -/
theorem productTV_const_eq_tailObjective (n : ℕ) {a b : ℝ}
    (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    productTV (fun _ : Fin n ↦ a) (fun _ ↦ b) =
      tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) := by
  rw [productTV_const_eq_countTV]
  exact countTV_eq_tailObjective
    ((admissiblePair_iff _ _).mpr (fun _ ↦ ⟨hb0, hba, ha1⟩))

end

end PoissonBinomialComparison
