import PoissonBinomialComparison.CommonMinimizer
import PoissonBinomialComparison.OneVectorConstant
import PoissonBinomialComparison.UpperInterior

/-!
# Reduction to an interior homogeneous changing vector

These wrappers combine the proved boundary reductions, stationarity and strict
likelihood-ratio argument under exactly the induction hypothesis in dimension
`n-1`. Reflection provides the lower-vector counterpart without assuming a
particular orientation of the minimizer.
-/

namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

/-- One changing vector of a global minimizer is homogeneous. -/
theorem IsGapMinimizer.one_changing_vector_constant (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n) :
    (∃ a : ℝ, ∀ i, q i < p i → p i = a) ∨
      (∃ b : ℝ, ∀ i, q i < p i → q i = b) := by
  have hb := hm.parameter_bounds hn hind h hg0
  obtain ⟨k,w,c,_,_,hw0,hw1,hc,_,_,_,hchanging,_⟩ :=
    exists_tail_kkt h (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) hg0
      (hm.tailObjective_lt_one hn hg0 hgn) hm.isLocalMinOn
  have hcard := hm.three_le_positiveGapCoordinates hn h hg0 hgn
  have hI : ∀ i ∈ positiveGapCoordinates p q, q i < p i := fun i hi ↦ (mem_filter.mp hi).2
  have hcst := exists_constant_vector_of_kkt h hcard hI hw0 hw1 hc
    (by assumption)
    (fun i hi ↦ ⟨(hchanging i (hI i hi)).1,(hchanging i (hI i hi)).2.2.1⟩)
    (fun i hi ↦ ⟨(hchanging i (hI i hi)).2.1,(hchanging i (hI i hi)).2.2.2⟩)
  simpa [positiveGapCoordinates] using hcst

/-- The constant upper value on the changing coordinates is strictly interior. -/
theorem IsGapMinimizer.upper_changing_constant_interior (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n)
    {a : ℝ} (hconst : ∀ i, q i < p i → p i = a) : 0 < a ∧ a < 1 := by
  obtain ⟨i,hi⟩ := exists_strict_coordinate_of_meanGap_pos h hg0
  have hb := hm.parameter_bounds hn hind h hg0
  have ha0 : 0 < a := hconst i hi ▸ (hb i).1
  have ha1 : a ≤ 1 := hconst i hi ▸ (h.1 i).2
  refine ⟨ha0,?_⟩
  by_cases hcommon : ∃ j, p j = q j
  · obtain ⟨k,w,c,hk0,hkn,hw0,hw1,hc,hk,hlast,_,hchanging,hcommonGrad⟩ :=
      exists_tail_kkt h (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) hg0
        (hm.tailObjective_lt_one hn hg0 hgn) hm.isLocalMinOn
    have hgrad : ∀ j, p j = q j → randomizedGradient p w k j = randomizedGradient q w k j ∧
        c ≤ randomizedGradient p w k j := by
      intro j hj
      obtain ⟨ν,hν,hP,hQ⟩ := hcommonGrad j hj
      exact ⟨hP.trans hQ.symm,by linarith⟩
    obtain ⟨hk1,_,hwlt,htie,hpos,_,hparams⟩ := common_coordinates_of_kkt hn hind h hm hg0
      (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) hw0 hw1 hc hk hlast hcommon hgrad
    have hk1n := ((mem_activeThresholds p q (k+1)).mp hk1).2.1
    exact homogeneous_upper_changing_lt_one h hk0 (by omega)
      (by have := hm.three_le_positiveGapCoordinates hn h hg0 hgn; omega) hwlt hconst
      (fun j hj ↦ (hparams j hj).1) (hm.upper_ne_one hn h hg0 hgn) hpos
      (fun j l hj hl ↦ (hchanging j hj).1.trans (hgrad l hl).2) htie
  · apply lt_of_le_of_ne ha1
    intro ha
    apply hm.upper_ne_one hn h hg0 hgn
    funext j
    have hj : q j < p j := lt_of_le_of_ne (h.2.2 j) (by
      intro heq
      exact hcommon ⟨j,heq.symm⟩)
    exact (hconst j hj).trans ha

/-- Reflection gives strict interiority of a homogeneous lower changing value. -/
theorem IsGapMinimizer.lower_changing_constant_interior (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n)
    {b : ℝ} (hconst : ∀ i, q i < p i → q i = b) : 0 < b ∧ b < 1 := by
  have hh := hm.reflection.upper_changing_constant_interior hn hind (admissiblePair_reflection h)
    (by simpa only [meanGap_reflection] using hg0)
    (by simpa only [meanGap_reflection] using hgn)
    (a := 1-b) (by
      intro i hi
      have hqi : q i < p i := by linarith
      simp only [hconst i hqi])
  constructor <;> linarith [hh.1,hh.2]

end

end PoissonBinomialComparison
