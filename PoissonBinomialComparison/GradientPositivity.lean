import PoissonBinomialComparison.ActiveThresholds
import PoissonBinomialComparison.RandomizedThreshold

/-!
# Positivity of the paired randomized gradients

If every upper parameter is positive and every lower parameter is below one,
the upper deletion law has positive top mass and the lower deletion law has
positive zero mass.  Interval support then shows that a common missing deletion
count would separate the full laws completely, forcing the tail objective to be
one.  Thus an objective below one gives strict paired-gradient positivity,
including deterministic boundary parameters.  The support argument does not
require that the deleted coordinate itself changes strictly.
-/

namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- The all-success count has the product of the success parameters as its mass. -/
theorem pbMassOn_card_eq_prod (p : ι → ℝ) (s : Finset ι) :
    pbMassOn p s s.card = ∏ i ∈ s, p i := by
  simp [pbMassOn, bernoulliWeight]

/-- Vanishing masses below a threshold force its upper tail to be one. -/
theorem pbTailOn_eq_one_of_mass_zero_below (p : ι → ℝ) (s : Finset ι) (k : ℕ)
    (hz : ∀ j < k, pbMassOn p s j = 0) : pbTailOn p s k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (fun j hj ↦ hz j (by omega))
    have hdiff := pbTailOn_sub_succ p s k
    rw [hz k (by omega), hprev] at hdiff
    linarith

/-- With positive top mass, a missing count places all support strictly above it. -/
theorem pbTailOn_succ_eq_one_of_mass_zero_of_top_pos {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {k : ℕ} (hk : k ≤ s.card)
    (htop : 0 < pbMassOn p s s.card) (hz : pbMassOn p s k = 0) :
    pbTailOn p s (k + 1) = 1 := by
  apply pbTailOn_eq_one_of_mass_zero_below
  intro j hj
  apply le_antisymm _ (pbMassOn_nonneg hp j)
  by_contra hnot
  have hpos := pbMassOn_positive_between s hp (by omega : j ≤ k) hk
    (lt_of_not_ge hnot) htop
  rw [hz] at hpos
  exact lt_irrefl _ hpos

/-- With positive zero mass, a missing count places all support strictly below it. -/
theorem pbTailOn_eq_zero_of_mass_zero_of_zero_pos {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {k : ℕ}
    (hzero : 0 < pbMassOn p s 0) (hz : pbMassOn p s k = 0) :
    pbTailOn p s k = 0 := by
  rw [pbTailOn_eq_sum_mass]
  apply sum_eq_zero
  intro j hj
  apply le_antisymm _ (pbMassOn_nonneg hp j)
  by_contra hnot
  have hpos := pbMassOn_positive_between s hp (Nat.zero_le k) (mem_Icc.mp hj).1
    hzero (lt_of_not_ge hnot)
  rw [hz] at hpos
  exact lt_irrefl _ hpos

variable {n : ℕ} {p q : Fin n → ℝ}

/-- At every manuscript threshold the two deleted masses have positive sum.
This holds even at coordinates with equal upper and lower parameters. -/
theorem deleted_mass_pair_pos (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    (hT : tailObjective p q < 1) (i : Fin n) {k : ℕ}
    (hk0 : 1 ≤ k) (hkn : k ≤ n) :
    0 < pbMassOn p (univ.erase i) (k - 1) +
      pbMassOn q (univ.erase i) (k - 1) := by
  let s := (univ : Finset (Fin n)).erase i
  have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 := fun j _ ↦ h.1 j
  have hqs : ∀ j ∈ s, 0 ≤ q j ∧ q j ≤ 1 := fun j _ ↦ h.2.1 j
  have hcard : s.card = n - 1 := by simp [s]
  have hk : k - 1 ≤ s.card := by omega
  have htop : 0 < pbMassOn p s s.card := by
    rw [pbMassOn_card_eq_prod]
    exact prod_pos fun j _ ↦ hp j
  have hzero : 0 < pbMassOn q s 0 := by
    rw [pbMassOn_zero]
    exact prod_pos fun j _ ↦ sub_pos.mpr (hq j)
  by_contra hnot
  have hpnonneg := pbMassOn_nonneg hps (k - 1)
  have hqnonneg := pbMassOn_nonneg hqs (k - 1)
  change ¬ 0 < pbMassOn p s (k - 1) + pbMassOn q s (k - 1) at hnot
  have hpz : pbMassOn p s (k - 1) = 0 := by linarith
  have hqz : pbMassOn q s (k - 1) = 0 := by linarith
  have hpk := pbTailOn_succ_eq_one_of_mass_zero_of_top_pos hps hk htop hpz
  have hqkm := pbTailOn_eq_zero_of_mass_zero_of_zero_pos hqs hzero hqz
  have hpstep := pbTailOn_sub_succ p s (k - 1)
  have hqstep := pbTailOn_sub_succ q s (k - 1)
  have hpred : k - 1 + 1 = k := by omega
  rw [hpred] at hpk hpstep hqstep
  have hpkm : pbTailOn p s (k - 1) = 1 := by linarith
  have hqk : pbTailOn q s k = 0 := by linarith
  have hpfull := pbTail_delete_succ p i (k - 1)
  have hqfull := pbTail_delete_succ q i (k - 1)
  change pbTail p (k - 1 + 1) = (1 - p i) * pbTailOn p s (k - 1 + 1) +
    p i * pbTailOn p s (k - 1) at hpfull
  change pbTail q (k - 1 + 1) = (1 - q i) * pbTailOn q s (k - 1 + 1) +
    q i * pbTailOn q s (k - 1) at hqfull
  rw [hpred, hpk, hpkm] at hpfull
  rw [hpred, hqk, hqkm] at hqfull
  have hbound := tailDiff_le_tailObjective p q (mem_Icc.mpr ⟨hk0, hkn⟩)
  unfold tailDiff at hbound
  rw [hpfull, hqfull] at hbound
  linarith

/-- Nonnegativity of every randomized coordinate gradient for valid parameters. -/
theorem randomizedGradient_nonneg (hp : ValidParameters p) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (k : ℕ) (i : Fin n) :
    0 ≤ randomizedGradient p w k i := by
  unfold randomizedGradient randomizedSlopeOn
  apply add_nonneg
  · exact mul_nonneg (sub_nonneg.mpr hw1) (pbMassOn_nonneg (fun j _ ↦ hp j) k)
  · apply mul_nonneg hw0
    split
    · exact le_rfl
    · exact pbMassOn_nonneg (fun j _ ↦ hp j) (k - 1)

/-- Every convex mixture of two admissible adjacent thresholds has positive
paired coordinate gradient when the objective is below one. -/
theorem randomizedGradient_pair_pos (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    (hT : tailObjective p q < 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {k : ℕ} (hk0 : 1 ≤ k) (hkn : k < n) (i : Fin n) :
    0 < randomizedGradient p w k i + randomizedGradient q w k i := by
  have hleft := deleted_mass_pair_pos h hp hq hT i hk0 hkn.le
  have hright := deleted_mass_pair_pos h hp hq hT i (by omega : 1 ≤ k + 1)
    (by omega : k + 1 ≤ n)
  simp only [Nat.add_sub_cancel] at hright
  unfold randomizedGradient randomizedSlopeOn
  simp only [show k ≠ 0 by omega, ite_false]
  by_cases hw : w = 1
  · subst w
    simpa using hleft
  · have hr := mul_pos (sub_pos.mpr (lt_of_le_of_ne hw1 hw)) hright
    have hl := mul_nonneg hw0 hleft.le
    nlinarith

/-- A pure threshold has positive paired gradient, including the final threshold. -/
theorem randomizedGradient_pair_pos_pure (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    (hT : tailObjective p q < 1) {k : ℕ} (hk0 : 1 ≤ k) (hkn : k ≤ n) (i : Fin n) :
    0 < randomizedGradient p 1 k i + randomizedGradient q 1 k i := by
  simpa [randomizedGradient, randomizedSlopeOn, show k ≠ 0 by omega] using
    deleted_mass_pair_pos h hp hq hT i hk0 hkn

/-- The multiplier bounding both coordinate gradients is strictly positive
(CPOS), for both adjacent mixtures and the pure final threshold. -/
theorem randomizedGradient_multiplier_pos (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    (hT : tailObjective p q < 1) {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {k : ℕ} (hk0 : 1 ≤ k) (hkn : k ≤ n) (hlast : k < n ∨ w = 1)
    (i : Fin n) (hpc : randomizedGradient p w k i ≤ c)
    (hqc : randomizedGradient q w k i ≤ c) : 0 < c := by
  have hpos : 0 < randomizedGradient p w k i + randomizedGradient q w k i := by
    rcases hlast with hk | rfl
    · exact randomizedGradient_pair_pos h hp hq hT hw0 hw1 hk0 hk i
    · exact randomizedGradient_pair_pos_pure h hp hq hT hk0 hkn i
  linarith

end

end PoissonBinomialComparison
