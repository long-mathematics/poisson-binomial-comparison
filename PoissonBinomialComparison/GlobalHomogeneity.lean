import PoissonBinomialComparison.MinimizerHomogeneitySetup
import PoissonBinomialComparison.LowerCoordinateClassification
import PoissonBinomialComparison.CommonHomogeneousCoordinates
import PoissonBinomialComparison.SplitPerturbation

/-! # Homogeneity of global minimizing pairs -/

namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

/-- All first-order and finite-law classification steps, isolating precisely
the second-variation exclusion of a repeated smaller positive lower value. -/
theorem IsGapMinimizer.lower_constant_of_upper_constant_of_no_smaller_repeat
    (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n - 1) → ℝ, AdmissiblePair r s →
      benchmark (n - 1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n)
    {a : ℝ} (hpa : ∀ i, q i < p i → p i = a)
    (hsmall : ∀ i j l, q i < p i → q j < p j → q l < p l →
      0 < q i → q i = q j → q i < q l → i = j) :
    ∃ b : ℝ, 0 < b ∧ b < a ∧ ∀ i, q i < p i → q i = b := by
  classical
  have ha := hm.upper_changing_constant_interior hn hind h hg0 hgn hpa
  have hb := hm.parameter_bounds hn hind h hg0
  obtain ⟨k, w, c, _, _, hw0, hw1, hc, hk, hlast, _, hchange, hcomm⟩ :=
    exists_tail_kkt h (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) hg0
      (hm.tailObjective_lt_one hn hg0 hgn) hm.isLocalMinOn
  have hgrad : ∀ i, p i = q i → randomizedGradient p w k i = randomizedGradient q w k i ∧
      c ≤ randomizedGradient p w k i := by
    intro i hi
    obtain ⟨ν, hν, hpν, hqν⟩ := hcomm i hi
    exact ⟨hpν.trans hqν.symm, by linarith⟩
  have hcommon : ∀ i, p i = q i → p i = w := by
    intro i hi
    obtain ⟨_, _, _, _, _, _, hall⟩ := common_coordinates_of_kkt hn hind h hm hg0
      (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) hw0 hw1 hc hk hlast ⟨i, hi⟩ hgrad
    exact (hall i hi).1
  let I := positiveGapCoordinates p q
  let C := univ \ I
  have hI : ∀ i, i ∈ I ↔ q i < p i := by simp [I, positiveGapCoordinates]
  have hC : ∀ i, i ∈ C ↔ p i = q i := by
    intro i
    simp only [C, mem_sdiff, mem_univ, true_and, hI]
    exact ⟨fun hn ↦ le_antisymm (le_of_not_gt hn) (h.2.2 i), fun heq ↦ by rw [heq]; exact lt_irrefl _⟩
  have hpart : univ = C ∪ I := by simp [C]
  have hCI : Disjoint C I := by
    apply disjoint_left.mpr
    intro i hiC hiI
    exact (mem_sdiff.mp hiC).2 hiI
  have hcard : 3 ≤ I.card := hm.three_le_positiveGapCoordinates hn h hg0 hgn
  obtain ⟨b, _, hba, hqb⟩ := lower_changing_coordinates_constant h.2.1 I C hpart hCI hcard
    ⟨hw0, hw1⟩ ha.2 hc k
    (fun i hi ↦ hcommon i ((hC i).mp hi))
    (fun i hi ↦ ((hC i).mp hi).symm.trans (hcommon i ((hC i).mp hi)))
    (fun i hi ↦ hpa i ((hI i).mp hi))
    (fun i hi ↦ by rw [← hpa i ((hI i).mp hi)]; exact (hI i).mp hi)
    (fun i hi ↦ (hchange i ((hI i).mp hi)).2.2.1 (by rw [hpa i ((hI i).mp hi)]; exact ha.2))
    (fun i hi hqi ↦ (hchange i ((hI i).mp hi)).2.2.2 hqi)
    (fun i hi _ ↦ (hchange i ((hI i).mp hi)).2.1)
    (fun i hi j hj l hl ↦ hsmall i j l ((hI i).mp hi) ((hI j).mp hj) ((hI l).mp hl))
  have hqb' : ∀ i, q i < p i → q i = b := fun i hi ↦ hqb i ((hI i).mpr hi)
  exact ⟨b, (hm.lower_changing_constant_interior hn hind h hg0 hgn hqb').1, hba, hqb'⟩

/-- QSPLIT's consequence for every interior-gap global minimizer. All active-set,
feasibility and multiplier hypotheses are supplied by the proved KKT theorem. -/
theorem IsGapMinimizer.no_repeated_smaller_lower (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n - 1) → ℝ, AdmissiblePair r s →
      benchmark (n - 1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n) :
    ∀ i j l, q i < p i → q j < p j → q l < p l →
      0 < q i → q i = q j → q i < q l → i = j := by
  have hb := hm.parameter_bounds hn hind h hg0
  obtain ⟨k, w, c, hk0, _, hw0, hw1, hc, _, _, _, hset, hchange, _⟩ :=
    exists_tail_kkt_with_activeSet h (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) hg0
      (hm.tailObjective_lt_one hn hg0 hgn) hm.isLocalMinOn
  intro i j l hi hj hl hi0 heq hlt
  exact eq_of_repeated_smaller_at_localMin h hm.isLocalMinOn hk0 hw0 hw1 hc hset
    hi0 heq hlt hi hj hl ((hchange i hi).2.2.2 hi0) ((hchange l hl).2.2.2 (hi0.trans hlt))

/-- When the upper changing vector is constant, the lower changing vector is
also constant and strictly interior; no second-variation assumptions remain. -/
theorem IsGapMinimizer.lower_constant_of_upper_constant (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n - 1) → ℝ, AdmissiblePair r s →
      benchmark (n - 1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n)
    {a : ℝ} (hpa : ∀ i, q i < p i → p i = a) :
    ∃ b : ℝ, 0 < b ∧ b < a ∧ ∀ i, q i < p i → q i = b :=
  hm.lower_constant_of_upper_constant_of_no_smaller_repeat hn hind h hg0 hgn hpa
    (hm.no_repeated_smaller_lower hn hind h hg0 hgn)

/-- Every global minimizer at an interior gap is a strictly interior homogeneous
pair. This is the manuscript's global stationary-point reduction, using only
the benchmark comparison in exactly the preceding dimension. -/
theorem IsGapMinimizer.homogeneous (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n - 1) → ℝ, AdmissiblePair r s →
      benchmark (n - 1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n) :
    ∃ a b : ℝ, 0 < b ∧ b < a ∧ a < 1 ∧ p = (fun _ ↦ a) ∧ q = (fun _ ↦ b) := by
  rcases hm.one_changing_vector_constant hn hind h hg0 hgn with ⟨a, hpa⟩ | ⟨b, hqb⟩
  · obtain ⟨b, hb0, hba, hqb⟩ := hm.lower_constant_of_upper_constant hn hind h hg0 hgn hpa
    have ha := hm.upper_changing_constant_interior hn hind h hg0 hgn hpa
    exact ⟨a, b, hb0, hba, ha.2, hm.homogeneous_of_changing_constants hn hind h hg0 hgn hpa hqb⟩
  · have hpa' : ∀ i, 1 - p i < 1 - q i → 1 - q i = 1 - b := by
      intro i hi
      rw [hqb i (by linarith)]
    obtain ⟨b', hb'0, hb'a, hqb'⟩ := hm.reflection.lower_constant_of_upper_constant hn hind
      (admissiblePair_reflection h) (by simpa only [meanGap_reflection] using hg0)
      (by simpa only [meanGap_reflection] using hgn) hpa'
    have hpa : ∀ i, q i < p i → p i = 1 - b' := by
      intro i hi
      have hh := hqb' i (by linarith)
      linarith
    have hb := hm.lower_changing_constant_interior hn hind h hg0 hgn hqb
    refine ⟨1 - b', b, hb.1, ?_, ?_, hm.homogeneous_of_changing_constants hn hind h hg0 hgn hpa hqb⟩
    · linarith
    · linarith

end

end PoissonBinomialComparison
