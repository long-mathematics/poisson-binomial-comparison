import PoissonBinomialComparison.CommonStationarity
import PoissonBinomialComparison.MinimizerReduction

/-!
# Common coordinates of a minimizing pair

A pure active test with stationary common coordinate would allow exact deletion
without changing the objective, contradicting strict dimension improvement.
Thus common coordinates require a tied adjacent pair and equal its randomizer.
-/

namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

/-- A pure active test cannot be stationary at a common coordinate of a global
minimizer. Equal positive deletion masses would contradict dimension improvement. -/
theorem IsGapMinimizer.not_pure_common_stationarity (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q) (hgap : 0 < meanGap p q)
    {k : ℕ} (hk : k ∈ activeThresholds p q) (i : Fin n) (hi : p i = q i)
    (hgrad : randomizedGradient p 1 k i = randomizedGradient q 1 k i)
    (hpos : 0 < randomizedGradient p 1 k i) : False := by
  have hk0 := ((mem_activeThresholds p q k).mp hk).1
  have hmass : pbMassOn p (univ.erase i) (k-1) = pbMassOn q (univ.erase i) (k-1) := by
    simpa [randomizedGradient,randomizedSlopeOn,show k ≠ 0 by omega] using hgrad
  have hmasspos : 0 < pbMassOn q (univ.erase i) (k-1) := by
    rw [hgrad] at hpos
    simpa [randomizedGradient,randomizedSlopeOn,show k ≠ 0 by omega] using hpos
  obtain ⟨r,s,hrs,hgap',hobj⟩ := exists_deleted_pair_of_stationary_active h i hi hk hmass hmasspos
  have hlow := hind r s hrs
  rw [hgap',hobj] at hlow
  have hbound := meanGap_le_dimension hrs
  rw [hgap'] at hbound
  have himprove := dimension_improvement (by omega : 2 ≤ n-1) hgap hbound
  rw [show n-1+1 = n by omega] at himprove
  obtain ⟨r',s',hrs',hg',ht'⟩ := himprove
  have hmin := hm r' s' hrs' hg'
  linarith

/-- All common coordinates equal the interior randomizer; their gradients are
the same positive tied mass, at least the positive gap multiplier. -/
theorem common_coordinates_of_kkt (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q) (hgap : 0 < meanGap p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    {k : ℕ} {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c)
    (hk : k ∈ activeThresholds p q) (hlast : w = 1 ∨ k+1 ∈ activeThresholds p q)
    (hcommon : ∃ i, p i = q i)
    (hgrad : ∀ i, p i = q i → randomizedGradient p w k i = randomizedGradient q w k i ∧
      c ≤ randomizedGradient p w k i) :
    k+1 ∈ activeThresholds p q ∧ 0 < w ∧ w < 1 ∧
      pbMass p k = pbMass q k ∧ 0 < pbMass p k ∧ c ≤ pbMass p k ∧
      ∀ i, p i = q i → p i = w ∧
        randomizedGradient p w k i = pbMass p k ∧ randomizedGradient q w k i = pbMass p k := by
  obtain ⟨i,hi⟩ := hcommon
  have hg := hgrad i hi
  have hpos := hc.trans_le hg.2
  have hwne : w ≠ 1 := by
    intro hw
    subst w
    exact hm.not_pure_common_stationarity hn hind h hgap hk i hi hg.1 hpos
  have hk1 := hlast.resolve_left hwne
  have hk' := (mem_activeThresholds p q k).mp hk
  have hk1' := (mem_activeThresholds p q (k+1)).mp hk1
  have hkn : k < n := by omega
  have hdiff := tailDiff_sub_succ p q k
  rw [hk'.2.2,hk1'.2.2,sub_self] at hdiff
  have htie : pbMass p k = pbMass q k := by linarith
  have hparam (j : Fin n) (hj : p j = q j) : p j = w := by
    have hs : ∃ l, l ≠ j ∧ q l < p l := by
      obtain ⟨l,hl⟩ := exists_strict_coordinate_of_meanGap_pos h hgap
      refine ⟨l,?_,hl⟩
      intro heq
      subst l
      linarith
    exact common_parameter_eq_weight h hp hq hw0 hw1 hk'.1 hkn htie j hj hs
      (hgrad j hj).1 (hc.trans_le (hgrad j hj).2)
  have hiw := hparam i hi
  have hmass := randomizedGradient_eq_mass_of_parameter_eq hk'.1 i hiw
  have hmp : 0 < pbMass p k := by rwa [hmass] at hpos
  have hmc : c ≤ pbMass p k := by simpa only [hmass] using hg.2
  refine ⟨hk1, hiw ▸ hp i, ?_, htie,hmp,hmc,?_⟩
  · rw [← hiw,hi]
    exact hq i
  · intro j hj
    have hjw := hparam j hj
    have hmj := randomizedGradient_eq_mass_of_parameter_eq hk'.1 j hjw
    exact ⟨hjw,hmj, (hgrad j hj).1.symm.trans hmj⟩

end

end PoissonBinomialComparison
