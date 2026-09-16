import PoissonBinomialComparison.LowerHomogeneity
import PoissonBinomialComparison.OtherVectorValues
import PoissonBinomialComparison.Deterministic

/-! # Finite coordinate patterns and homogeneous blocks -/

namespace PoissonBinomialComparison

open Finset

noncomputable section

/-- The manuscript's `g_M` with the background `Bin(s+1,w)`, including endpoint
values of the randomizing parameter. -/
def binomialBackgroundMass (s : ℕ) (w : ℝ) (M : ℕ) (t : ℝ) (k : ℤ) : ℝ :=
  homogeneousBlockMass (fun _ : Fin (s + 1) ↦ w) univ M t k

variable {ι : Type*} [DecidableEq ι]

/-- Adding zero coordinates does not change the randomized count law. -/
theorem randomizedMassIntOn_union_zero (p : ι → ℝ) (S Z : Finset ι) (w : ℝ)
    (hz : ∀ i ∈ Z, p i = 0) (k : ℤ) :
    randomizedMassIntOn p (S ∪ Z) w k = randomizedMassIntOn p S w k := by
  induction Z using Finset.induction_on with
  | empty => simp
  | @insert i Z hi ih =>
    rw [union_insert]
    by_cases him : i ∈ S ∪ Z
    · rw [insert_eq_of_mem him]
      exact ih (fun j hj ↦ hz j (mem_insert_of_mem hj))
    · rw [randomizedMassIntOn_insert p him, hz i (mem_insert_self _ _)]
      simp only [sub_zero, one_mul, zero_mul, add_zero]
      exact ih (fun j hj ↦ hz j (mem_insert_of_mem hj))

/-- A common block plus the randomizing Bernoulli is one larger binomial block. -/
theorem randomizedMassIntOn_common (p : ι → ℝ) (C : Finset ι) (w : ℝ)
    (hc : ∀ i ∈ C, p i = w) (k : ℤ) :
    randomizedMassIntOn p C w k =
      pbMassIntOn (fun _ : Fin (C.card + 1) ↦ w) univ k := by
  rw [← homogeneousBlockMass_empty_eq_pbMassInt p]
  induction C using Finset.induction_on generalizing k with
  | empty => simp [randomizedMassIntOn, bernoulliConvolve, homogeneousBlockMass_succ]
  | @insert i C hi ih =>
    rw [card_insert_of_notMem hi, randomizedMassIntOn_insert p hi, hc i (mem_insert_self _ _),
      homogeneousBlockMass_succ]
    rw [ih (fun j hj ↦ hc j (mem_insert_of_mem hj)), ih (fun j hj ↦ hc j (mem_insert_of_mem hj))]

/-- Exact bridge from a common block and homogeneous changing block to `g_M`. -/
theorem randomizedMassIntOn_common_union (p : ι → ℝ) (C H : Finset ι) (w t : ℝ)
    (hdisj : Disjoint C H) (hc : ∀ i ∈ C, p i = w) (hh : ∀ i ∈ H, p i = t) (k : ℤ) :
    randomizedMassIntOn p (C ∪ H) w k = binomialBackgroundMass C.card w H.card t k := by
  induction H using Finset.induction_on generalizing k with
  | empty => simpa [binomialBackgroundMass] using randomizedMassIntOn_common p C w hc k
  | @insert i H hi ih =>
    have hiC : i ∉ C := fun hic ↦ disjoint_left.mp hdisj hic (mem_insert_self _ _)
    have hdisj' : Disjoint C H := hdisj.mono_right (subset_insert _ _)
    have hh' : ∀ j ∈ H, p j = t := fun j hj ↦ hh j (mem_insert_of_mem hj)
    rw [union_insert, randomizedMassIntOn_insert p (by simp [hiC, hi]),
      hh i (mem_insert_self _ _), card_insert_of_notMem hi]
    simp only [binomialBackgroundMass, homogeneousBlockMass_succ]
    rw [ih hdisj' hh', ih hdisj' hh']
    rfl

/-- Zero coordinates are removed exactly before evaluating the homogeneous block. -/
theorem randomizedMassIntOn_pattern (p : ι → ℝ) (C H Z : Finset ι) (w t : ℝ)
    (hdisj : Disjoint C H) (hc : ∀ i ∈ C, p i = w) (hh : ∀ i ∈ H, p i = t)
    (hz : ∀ i ∈ Z, p i = 0) (k : ℤ) :
    randomizedMassIntOn p (C ∪ H ∪ Z) w k = binomialBackgroundMass C.card w H.card t k := by
  rw [randomizedMassIntOn_union_zero p (C ∪ H) Z w hz,
    randomizedMassIntOn_common_union p C H w t hdisj hc hh]

/-- A constant background law depends only on its number of coordinates. -/
theorem pbMassIntOn_common_card (p : ι → ℝ) (C : Finset ι) (w : ℝ)
    (hc : ∀ i ∈ C, p i = w) (k : ℤ) :
    pbMassIntOn p C k = pbMassIntOn (fun _ : Fin C.card ↦ w) univ k := by
  rw [← homogeneousBlockMass_empty_eq_pbMassInt p]
  symm
  simpa using homogeneousBlockMass_eq_union p ∅ C (by simp) w hc k

/-- Canonical binomial backgrounds are equivalent to adjoining one actual
coordinate to a common block in any ambient finite index type. -/
theorem binomialBackgroundMass_eq_insert_common (p : ι → ℝ) (C : Finset ι)
    {z : ι} (hz : z ∉ C) (w : ℝ) (hc : ∀ i ∈ C, p i = w) (hzv : p z = w)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    binomialBackgroundMass C.card w M t k = homogeneousBlockMass p (insert z C) M t k := by
  induction M generalizing k with
  | zero =>
    simp only [binomialBackgroundMass, homogeneousBlockMass_zero]
    rw [← homogeneousBlockMass_empty_eq_pbMassInt p]
    have hh := homogeneousBlockMass_eq_union p ∅ (insert z C) (by simp) w
      (fun i hi ↦ by rcases mem_insert.mp hi with rfl | hi; exact hzv; exact hc i hi) k
    rw [card_insert_of_notMem hz] at hh
    simpa using hh
  | succ M ih =>
    simp only [binomialBackgroundMass, homogeneousBlockMass_succ] at ih ⊢
    rw [ih, ih]

variable {n : ℕ}

/-- Coordinate gradients with a common/positive/zero deletion pattern are the
exact background-binomial block masses. -/
theorem randomizedGradient_pattern (p : Fin n → ℝ) (C H Z : Finset (Fin n)) (i : Fin n)
    (w t : ℝ) (k : ℕ) (hpart : univ.erase i = C ∪ H ∪ Z)
    (hdisj : Disjoint C H) (hc : ∀ j ∈ C, p j = w) (hh : ∀ j ∈ H, p j = t)
    (hz : ∀ j ∈ Z, p j = 0) :
    randomizedGradient p w k i = binomialBackgroundMass C.card w H.card t k := by
  rw [randomizedGradient, ← randomizedMassIntOn_natCast, hpart]
  exact randomizedMassIntOn_pattern p C H Z w t hdisj hc hh hz k

/-- The mixed coefficient with a common/positive/zero double-deletion pattern
is the adjacent difference of the exact same background-binomial law. -/
theorem randomizedMixedCoefficient_pattern (p : Fin n → ℝ) (C H Z : Finset (Fin n))
    (i j : Fin n) (w t : ℝ) (k : ℕ) (hpart : (univ.erase i).erase j = C ∪ H ∪ Z)
    (hdisj : Disjoint C H) (hc : ∀ l ∈ C, p l = w) (hh : ∀ l ∈ H, p l = t)
    (hz : ∀ l ∈ Z, p l = 0) :
    randomizedMixedCoefficient p w k i j =
      binomialBackgroundMass C.card w H.card t ((k : ℤ) - 1) -
        binomialBackgroundMass C.card w H.card t k := by
  rw [randomizedMixedCoefficient, randomizedCoefficientOn_eq_int, hpart]
  rw [randomizedMassIntOn_pattern p C H Z w t hdisj hc hh hz,
    randomizedMassIntOn_pattern p C H Z w t hdisj hc hh hz]

/-- QONE on actual coordinate laws: one smaller positive lower value, a
nonempty larger block, and arbitrary zeros cannot satisfy the free gradients. -/
theorem not_two_positive_coordinate_pattern (p q : Fin n → ℝ)
    (C H Z : Finset (Fin n)) (i : Fin n) {w u v a c : ℝ} (k : ℕ)
    (hpart : univ = insert i (C ∪ H ∪ Z)) (hi : i ∉ C ∪ H ∪ Z)
    (hCH : Disjoint C H) (hCZ : Disjoint C Z) (hHZ : Disjoint H Z)
    (hH : H.Nonempty) (hr : 3 ≤ H.card + Z.card + 1)
    (hw : 0 ≤ w ∧ w ≤ 1) (hu : 0 < u) (huv : u < v) (hva : v < a) (ha : a < 1)
    (hc : 0 < c) (hpC : ∀ l ∈ C, p l = w) (hqC : ∀ l ∈ C, q l = w)
    (hpI : ∀ l ∈ H ∪ Z, p l = a) (hqi : q i = u)
    (hqH : ∀ l ∈ H, q l = v) (hqZ : ∀ l ∈ Z, q l = 0)
    (hpiGrad : randomizedGradient p w k i = c)
    (hqiGrad : randomizedGradient q w k i = c)
    (hqHGrad : ∀ l ∈ H, randomizedGradient q w k l = c) : False := by
  have hdel : univ.erase i = C ∪ H ∪ Z := by rw [hpart, erase_insert hi]
  have hvg := randomizedGradient_pattern q C H Z i w v k hdel hCH hqC hqH hqZ
  have hag := randomizedGradient_pattern p C (H ∪ Z) ∅ i w a k
    (by simpa [union_assoc] using hdel) (disjoint_union_right.mpr ⟨hCH, hCZ⟩)
    hpC hpI (by simp)
  rw [card_union_of_disjoint hHZ] at hag
  obtain ⟨j, hj⟩ := hH
  have hij : i ≠ j := by intro heq; subst j; exact hi (by simp [hj])
  have hjC : j ∉ C := fun hjC ↦ disjoint_left.mp hCH hjC hj
  have hjZ : j ∉ Z := fun hjZ ↦ disjoint_left.mp hHZ hj hjZ
  have hdel2 : (univ.erase i).erase j = C ∪ H.erase j ∪ Z := by
    rw [hdel, erase_union_distrib, erase_union_distrib, erase_eq_of_notMem hjC, erase_eq_of_notMem hjZ]
  have hcoef := randomizedMixedCoefficient_pattern q C (H.erase j) Z i j w v k hdel2
    (hCH.mono_right (erase_subset _ _)) hqC
    (fun l hl ↦ hqH l (mem_erase.mp hl).2) hqZ
  rw [card_erase_of_mem hj] at hcoef
  have hgrad := randomizedGradient_sub q hij w k
  rw [hqiGrad, hqHGrad j hj, hqH j hj, hqi, sub_self] at hgrad
  have hcoef0 : randomizedMixedCoefficient q w k i j = 0 :=
    (mul_eq_zero.mp hgrad.symm).resolve_left (sub_pos.mpr huv).ne'
  have hd : deriv (fun t ↦ binomialBackgroundMass C.card w H.card t k) v = 0 := by
    simp only [binomialBackgroundMass, deriv_homogeneousBlockMass]
    change (H.card : ℝ) *
      (binomialBackgroundMass C.card w (H.card - 1) v ((k : ℤ) - 1) -
        binomialBackgroundMass C.card w (H.card - 1) v k) = 0
    rw [← hcoef, hcoef0, mul_zero]
  exact not_lower_two_values_stationary (fun _ _ ↦ hw) (by simpa using card_pos.mpr ⟨j, hj⟩)
    hr (hu.trans huv) hva ha hc k (hvg.symm.trans hqiGrad) (hag.symm.trans hpiGrad) hd

/-- QZERO on actual coordinate laws: a nonempty positive lower block and a
nonempty zero block contradict the upper free gradient and zero-coordinate KKT. -/
theorem not_positive_zero_coordinate_pattern (p q : Fin n → ℝ)
    (C H Z : Finset (Fin n)) {w v a c : ℝ} (k : ℕ)
    (hpart : univ = C ∪ H ∪ Z)
    (hCH : Disjoint C H) (hCZ : Disjoint C Z) (hHZ : Disjoint H Z)
    (hH : H.Nonempty) (hZ : Z.Nonempty) (hr : 3 ≤ H.card + Z.card)
    (hw : 0 ≤ w ∧ w ≤ 1) (hv : 0 < v) (hva : v < a) (ha : a < 1)
    (hc : 0 < c) (hpC : ∀ l ∈ C, p l = w) (hqC : ∀ l ∈ C, q l = w)
    (hpI : ∀ l ∈ H ∪ Z, p l = a)
    (hqH : ∀ l ∈ H, q l = v) (hqZ : ∀ l ∈ Z, q l = 0)
    (hpHGrad : ∀ l ∈ H, randomizedGradient p w k l = c)
    (hqHGrad : ∀ l ∈ H, randomizedGradient q w k l = c)
    (hqZGrad : ∀ l ∈ Z, randomizedGradient q w k l ≤ c) : False := by
  obtain ⟨i, hi⟩ := hH
  obtain ⟨j, hj⟩ := hZ
  have hiC : i ∉ C := fun hic ↦ disjoint_left.mp hCH hic hi
  have hiZ : i ∉ Z := fun hiz ↦ disjoint_left.mp hHZ hi hiz
  have hjC : j ∉ C := fun hjc ↦ disjoint_left.mp hCZ hjc hj
  have hjH : j ∉ H := fun hjh ↦ disjoint_left.mp hHZ hjh hj
  have hdeli : univ.erase i = C ∪ H.erase i ∪ Z := by
    rw [hpart, erase_union_distrib, erase_union_distrib, erase_eq_of_notMem hiC, erase_eq_of_notMem hiZ]
  have hdelj : univ.erase j = C ∪ H ∪ Z.erase j := by
    rw [hpart, erase_union_distrib, erase_union_distrib, erase_eq_of_notMem hjC, erase_eq_of_notMem hjH]
  have hvg := randomizedGradient_pattern q C (H.erase i) Z i w v k hdeli
    (hCH.mono_right (erase_subset _ _)) hqC (fun l hl ↦ hqH l (mem_erase.mp hl).2) hqZ
  rw [card_erase_of_mem hi] at hvg
  have hzg := randomizedGradient_pattern q C H (Z.erase j) j w v k hdelj hCH hqC hqH
    (fun l hl ↦ hqZ l (mem_erase.mp hl).2)
  have hag := randomizedGradient_pattern p C (H.erase i ∪ Z) ∅ i w a k
    (by simpa [union_assoc] using hdeli)
    (disjoint_union_right.mpr ⟨hCH.mono_right (erase_subset _ _), hCZ⟩)
    hpC (fun l hl ↦ hpI l (by
      rcases mem_union.mp hl with hl | hl
      · exact mem_union_left _ (mem_erase.mp hl).2
      · exact mem_union_right _ hl)) (by simp)
  rw [card_union_of_disjoint (hHZ.mono_left (erase_subset _ _)), card_erase_of_mem hi] at hag
  have hcard : H.card - 1 + Z.card = H.card + Z.card - 1 := by
    have hh := card_pos.mpr ⟨i, hi⟩
    omega
  rw [hcard] at hag
  exact not_lower_positive_and_zero_stationary (fun _ _ ↦ hw)
    (by simpa using card_pos.mpr ⟨i, hi⟩) (by simpa using card_pos.mpr ⟨j, hj⟩)
    hr hv hva ha hc k (hvg.symm.trans (hqHGrad i hi))
    (by change binomialBackgroundMass C.card w H.card v k ≤ c; rw [← hzg]; exact hqZGrad j hj) (hag.symm.trans (hpHGrad i hi))

end

end PoissonBinomialComparison
