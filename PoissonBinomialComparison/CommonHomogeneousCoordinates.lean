import PoissonBinomialComparison.BlockCoordinates
import PoissonBinomialComparison.NoCommonCoordinates
import PoissonBinomialComparison.MinimizerHomogeneitySetup

/-! # Homogeneous changing blocks leave no common coordinates

The full coordinate laws and gradients are identified with the scalar block
laws before applying the no-common-block obstruction. The only induction
hypothesis is the benchmark lower bound in the preceding dimension.
-/

namespace PoissonBinomialComparison

open Finset

private theorem block_congr_background {ι : Type*} [DecidableEq ι]
    {p q : ι → ℝ} {s : Finset ι} (h : ∀ i ∈ s, p i = q i)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    homogeneousBlockMass p s M t k = homogeneousBlockMass q s M t k := by
  induction M generalizing k with
  | zero => exact pbMassIntOn_congr h k
  | succ M ih => simp only [homogeneousBlockMass_succ, ih]

private theorem mass_pos_interior {ι : Type*} [DecidableEq ι]
    {p : ι → ℝ} (s : Finset ι) (hp : ∀ i ∈ s, 0 < p i ∧ p i < 1)
    {k : ℕ} (hk : k ≤ s.card) : 0 < pbMassOn p s k := by
  apply pbMassOn_positive_between s (fun i hi => ⟨(hp i hi).1.le,(hp i hi).2.le⟩)
    (Nat.zero_le k) hk
  · rw [pbMassOn_zero]
    exact prod_pos fun i hi => sub_pos.mpr (hp i hi).2
  · rw [pbMassOn_card_eq_prod]
    exact prod_pos fun i hi => (hp i hi).1

/-- A minimizing pair whose two changing vectors are constant has no unchanged coordinate. -/
theorem IsGapMinimizer.no_common_of_changing_constants {n : ℕ} (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n)
    {a b : ℝ} (hpa : ∀ i, q i < p i → p i = a)
    (hqb : ∀ i, q i < p i → q i = b) : ∀ i, q i < p i := by
  have ha := hm.upper_changing_constant_interior hn hind h hg0 hgn hpa
  have hb := hm.lower_changing_constant_interior hn hind h hg0 hgn hqb
  obtain ⟨i,hi⟩ := exists_strict_coordinate_of_meanGap_pos h hg0
  have hba : b < a := by simpa only [hpa i hi,hqb i hi] using hi
  by_contra hnot
  push Not at hnot
  obtain ⟨l,hl⟩ := hnot
  have hlcommon : p l = q l := le_antisymm hl (h.2.2 l)
  have hbds := hm.parameter_bounds hn hind h hg0
  obtain ⟨k,w,c,hk0,hkn,hw0,hw1,hc,hactive,hlast,_,hchanging,hcommonGrad⟩ :=
    exists_tail_kkt h (fun j => (hbds j).1) (fun j => (hbds j).2) hg0
      (hm.tailObjective_lt_one hn hg0 hgn) hm.isLocalMinOn
  have hgrad : ∀ j, p j = q j → randomizedGradient p w k j = randomizedGradient q w k j ∧
      c ≤ randomizedGradient p w k j := by
    intro j hj
    obtain ⟨ν,hν,hP,hQ⟩ := hcommonGrad j hj
    exact ⟨hP.trans hQ.symm,by linarith⟩
  obtain ⟨hactive1,hwpos,hwlt,htie,_,hcmass,hparams⟩ :=
    common_coordinates_of_kkt hn hind h hm hg0 (fun j => (hbds j).1)
      (fun j => (hbds j).2) hw0 hw1 hc hactive hlast ⟨l,hlcommon⟩ hgrad
  have hkn' : k < n := by have := ((mem_activeThresholds p q (k+1)).mp hactive1).2.1; omega
  let C := (univ : Finset (Fin n)).filter (fun j => p j = q j)
  let I := positiveGapCoordinates p q
  let H := I.erase i
  have hiI : i ∈ I := by simp [I,positiveGapCoordinates,hi]
  have hiC : i ∉ C := by simp [C,ne_of_gt hi]
  have hC (j : Fin n) (hj : j ∈ C) : p j = q j := (mem_filter.mp hj).2
  have hI (j : Fin n) (hj : j ∈ I) : q j < p j := (mem_filter.mp hj).2
  have hpart : univ.erase i = C ∪ H := by
    ext j
    simp only [mem_erase,mem_univ,and_true,true_and,mem_union,H,C,mem_filter,mem_univ,true_and]
    constructor
    · intro hji
      rcases (h.2.2 j).eq_or_lt with heq | hlt
      · exact Or.inl heq.symm
      · exact Or.inr ⟨hji,by simp [I,positiveGapCoordinates,hlt]⟩
    · rintro (heq | ⟨hji,_⟩)
      · intro heji; subst j; exact hi.ne' heq
      · exact hji
  have hdisj : Disjoint C H := by
    apply disjoint_left.mpr
    intro j hjC hjH
    have hh := hI j (mem_erase.mp hjH).2
    rw [hC j hjC] at hh
    exact lt_irrefl _ hh
  have hcard : 2 ≤ H.card := by
    have hh := hm.three_le_positiveGapCoordinates hn h hg0 hgn
    change 3 ≤ I.card at hh
    simpa only [H,card_erase_of_mem hiI] using (show 2 ≤ I.card-1 by omega)
  have hsize : H.card-2+2 = H.card := by omega
  have hcP : ∀ j ∈ C, p j = w := fun j hj => (hparams j (hC j hj)).1
  have hcQ : ∀ j ∈ C, q j = w := fun j hj => (hC j hj).symm.trans (hcP j hj)
  have hhP : ∀ j ∈ H, p j = a := fun j hj => hpa j (hI j (mem_erase.mp hj).2)
  have hhQ : ∀ j ∈ H, q j = b := fun j hj => hqb j (hI j (mem_erase.mp hj).2)
  let P : Fin n → ℝ := fun _ => w
  have bridge (v : Fin n → ℝ) (t : ℝ) (hvC : ∀ j ∈ C, v j = w)
      (hvH : ∀ j ∈ H, v j = t) (z : ℤ) :
      homogeneousBlockMass P C H.card t z = pbMassIntOn v (univ.erase i) z := by
    rw [block_congr_background (q := v) (fun j hj => (hvC j hj).symm)]
    rw [homogeneousBlockMass_eq_union v C H hdisj t hvH,← hpart]
  have gradbridge (v : Fin n → ℝ) (t : ℝ) (hvC : ∀ j ∈ C, v j = w)
      (hvH : ∀ j ∈ H, v j = t) :
      homogeneousBlockMass P (insert i C) H.card t k = randomizedGradient v w k i := by
    rw [randomizedGradient_pattern v C H ∅ i w t k (by simpa using hpart)
      hdisj hvC hvH (by simp)]
    exact (binomialBackgroundMass_eq_insert_common P C hiC w (fun _ _ => rfl) rfl _ _ _).symm
  have hgP : randomizedGradient p w k i = c := (hchanging i hi).2.2.1 (by rw [hpa i hi]; exact ha.2)
  have hgQ : randomizedGradient q w k i = c := (hchanging i hi).2.2.2 (by rw [hqb i hi]; exact hb.1)
  have hqinterior : ∀ j, 0 < q j ∧ q j < 1 := by
    intro j
    rcases (h.2.2 j).eq_or_lt with heq | hlt
    · have hwj := (hparams j heq.symm).1
      rw [heq,hwj]; exact ⟨hwpos,hwlt⟩
    · rw [hqb j hlt]; exact hb
  have hpred : (k : ℤ)-1 = ((k-1 : ℕ) : ℤ) := by omega
  have hpos (z : ℕ) (hz : z ≤ n-1) : 0 < homogeneousBlockMass P C H.card b z := by
    rw [bridge q b hcQ hhQ,pbMassIntOn_natCast]
    exact mass_pos_interior _ (fun j _ => hqinterior j) (by simpa using hz)
  have hnu (v : Fin n → ℝ) (t : ℝ) (hvi : v i = t)
      (hvC : ∀ j ∈ C, v j = w) (hvH : ∀ j ∈ H, v j = t)
      (hgv : randomizedGradient v w k i = c) (hmv : c ≤ pbMass v k) :
      0 ≤ (t-w) * (homogeneousBlockMass P C H.card t ((k : ℤ)-1) -
        homogeneousBlockMass P C H.card t k) := by
    rw [hpred,bridge v t hvC hvH,bridge v t hvC hvH,pbMassIntOn_natCast,pbMassIntOn_natCast]
    have hrec := pbMass_delete_succ v i (k-1)
    rw [show k-1+1=k by omega,hvi] at hrec
    simp only [randomizedGradient,randomizedSlopeOn,show k ≠ 0 by omega,ite_false] at hgv
    nlinarith only [hrec,hgv,hmv]
  apply homogeneous_blocks_common_multiplier_impossible hiC (fun _ _ => ⟨hw0,hw1⟩)
    (H.card-2) hb.1 hba ha.2 hwpos hwlt (show P i=w from rfl) (k : ℤ)
  · rw [hsize,hpred]; exact hpos (k-1) (by omega)
  · rw [hsize]; exact hpos k (by omega)
  · rw [hsize,gradbridge q b hcQ hhQ,gradbridge p a hcP hhP,hgP,hgQ]
  · rw [hsize]; exact hnu p a (hpa i hi) hcP hhP hgP hcmass
  · rw [hsize]; exact hnu q b (hqb i hi) hcQ hhQ hgQ (by rwa [← htie])

/-- With both changing blocks constant, the entire minimizing pair is homogeneous. -/
theorem IsGapMinimizer.homogeneous_of_changing_constants {n : ℕ} (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n)
    {a b : ℝ} (hpa : ∀ i, q i < p i → p i = a)
    (hqb : ∀ i, q i < p i → q i = b) :
    p = (fun _ => a) ∧ q = (fun _ => b) := by
  have hc := hm.no_common_of_changing_constants hn hind h hg0 hgn hpa hqb
  exact ⟨funext (fun i => hpa i (hc i)),funext (fun i => hqb i (hc i))⟩

end PoissonBinomialComparison
