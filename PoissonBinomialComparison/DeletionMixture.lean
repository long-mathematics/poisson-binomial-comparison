import PoissonBinomialComparison.RandomizedThreshold
import PoissonBinomialComparison.ActiveThresholds
import PoissonBinomialComparison.Reindex
import PoissonBinomialComparison.MaximalAtom

/-!
# Midpoint deletion mixtures with at most two positive gaps

For two varying coordinates, the tail polynomial is quadratic and its symmetric
difference is exactly its midpoint gradient applied to the gap vector. The
resulting two-term deletion mixture is a Bernoulli sum directly: factor out the
common deleted law and combine the two remaining Bernoulli parameters. No
general real-rootedness theorem is needed.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Coordinatewise midpoint of two parameter vectors. -/
def midpointParameters (p q : ι → ℝ) (i : ι) : ℝ := (p i + q i) / 2

omit [DecidableEq ι] in
theorem midpointParameters_valid {p q : ι → ℝ}
    (hp : ValidParameters p) (hq : ValidParameters q) :
    ValidParameters (midpointParameters p q) := by
  intro i
  have hp' := hp i
  have hq' := hq i
  simp only [midpointParameters]
  constructor <;> linarith

private theorem coefficient_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (k : ℕ) :
    randomizedCoefficientOn p s 0 k = randomizedCoefficientOn q s 0 k := by
  simp only [randomizedCoefficientOn, randomizedSlopeOn, pbMassOn_congr h]

/-- The count mass is affine in each coordinate, with its exact coefficient. -/
theorem pbMassOn_insert_affine (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (k : ℕ) :
    pbMassOn p (insert i s) k = pbMassOn p s k +
      p i * randomizedCoefficientOn p s 0 k := by
  simpa [randomizedSlopeOn] using randomizedSlopeOn_insert p hi 0 k

/-- The exact quadratic tail polynomial in two inserted parameters. -/
theorem pbTailOn_insert_insert_polynomial (p : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j) (k : ℕ) :
    pbTailOn p (insert i (insert j s)) (k + 1) = pbTailOn p s (k + 1) +
      (p i + p j) * pbMassOn p s k + p i * p j * randomizedCoefficientOn p s 0 k := by
  simpa [randomizedTailOn, randomizedSlopeOn] using
    randomizedTailOn_insert_insert p hi hj hij 0 k

/-- Two-coordinate midpoint identity on an arbitrary common coordinate set. -/
theorem pbTailOn_two_coordinate_midpoint (p q : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j)
    (heq : ∀ l ∈ s, p l = q l) (k : ℕ) :
    pbTailOn p (insert i (insert j s)) (k + 1) -
      pbTailOn q (insert i (insert j s)) (k + 1) =
        (p i - q i) * pbMassOn (midpointParameters p q) (insert j s) k +
        (p j - q j) * pbMassOn (midpointParameters p q) (insert i s) k := by
  have hpr : ∀ l ∈ s, p l = midpointParameters p q l := by
    intro l hl
    simp only [midpointParameters, ← heq l hl]
    ring
  have hqr : ∀ l ∈ s, q l = midpointParameters p q l :=
    fun l hl ↦ (heq l hl).symm.trans (hpr l hl)
  rw [pbTailOn_insert_insert_polynomial p hi hj hij,
    pbTailOn_insert_insert_polynomial q hi hj hij,
    pbMassOn_insert_affine _ hj, pbMassOn_insert_affine _ hi,
    pbTailOn_congr hpr, pbTailOn_congr hqr, pbMassOn_congr hpr,
    pbMassOn_congr hqr, coefficient_congr hpr, coefficient_congr hqr]
  simp only [midpointParameters]
  ring

/-- A convex combination of two single-Bernoulli extensions is itself one
Bernoulli extension, with the averaged parameter. -/
theorem pbMassOn_two_deletion_mixture (r : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (u v : ℝ) (huv : u + v = 1) (k : ℕ) :
    u * pbMassOn r (insert j s) k + v * pbMassOn r (insert i s) k =
      pbMassOn (Function.update r j (u * r j + v * r i)) (insert j s) k := by
  have hr : ∀ l ∈ s, Function.update r j (u * r j + v * r i) l = r l := by
    intro l hl
    have hlj : l ≠ j := by intro he; subst l; exact hj hl
    exact Function.update_of_ne hlj _ r
  rw [pbMassOn_insert_affine r hj, pbMassOn_insert_affine r hi,
    pbMassOn_insert_affine _ hj, pbMassOn_congr hr, coefficient_congr hr,
    Function.update_self]
  calc
    _ = (u + v) * pbMassOn r s k +
        (u * r j + v * r i) * randomizedCoefficientOn r s 0 k := by ring
    _ = _ := by rw [huv]; ring

/-- The combined Bernoulli parameter remains valid for nonnegative mixture weights. -/
theorem two_deletion_mixture_valid {r : ι → ℝ} (hr : ValidParameters r)
    (i j : ι) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    ValidParameters (Function.update r j (u * r j + v * r i)) := by
  intro l
  by_cases hl : l = j
  · subst l
    rw [Function.update_self]
    constructor
    · exact add_nonneg (mul_nonneg hu (hr j).1) (mul_nonneg hv (hr i).1)
    · calc
        u * r j + v * r i ≤ u * 1 + v * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hr j).2 hu)
            (mul_le_mul_of_nonneg_left (hr i).2 hv)
        _ = 1 := by simpa using huv
  · simpa [Function.update_of_ne hl] using hr l

variable {n : ℕ}

/-- Coordinates with a positive gap in the manuscript's ordered pair. -/
def positiveGapCoordinates (p q : Fin n → ℝ) : Finset (Fin n) :=
  univ.filter (fun i ↦ q i < p i)

/-- Normalized coordinate gaps, with Lean's total division convention at zero gap. -/
def gapWeights (p q : Fin n → ℝ) (i : Fin n) : ℝ := (p i - q i) / meanGap p q

/-- A finite mixture of laws obtained by deleting one coordinate. -/
def deletionMixture (r w : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i, w i * pbMassOn r (univ.erase i) k

theorem gapWeights_nonneg {p q : Fin n → ℝ} (h : AdmissiblePair p q) (i : Fin n) :
    0 ≤ gapWeights p q i :=
  div_nonneg (sub_nonneg.mpr (h.2.2 i)) (meanGap_nonneg h)

theorem sum_gapWeights {p q : Fin n → ℝ} (hgap : meanGap p q ≠ 0) :
    ∑ i, gapWeights p q i = 1 := by
  simp only [gapWeights, div_eq_mul_inv, ← sum_mul, ← meanGap_eq_sum]
  exact mul_inv_cancel₀ hgap

private theorem sum_eq_two {f : Fin n → ℝ} {i j : Fin n} (hij : i ≠ j)
    (hz : ∀ l, l ≠ i → l ≠ j → f l = 0) : ∑ l, f l = f i + f j := by
  have hs : ∑ l ∈ ({i, j} : Finset (Fin n)), f l = ∑ l, f l := by
    apply sum_subset (subset_univ _)
    intro l _ hl
    have hli : l ≠ i := by intro he; subst l; exact hl (by simp)
    have hlj : l ≠ j := by intro he; subst l; exact hl (by simp)
    exact hz l hli hlj
  rw [← hs]
  simp [hij]

/-- Full-coordinate two-gap midpoint identity, before division by the total gap. -/
theorem tailDiff_two_coordinate_midpoint (p q : Fin n → ℝ) {i j : Fin n}
    (hij : i ≠ j) (heq : ∀ l, l ≠ i → l ≠ j → p l = q l) (k : ℕ) :
    tailDiff p q (k + 1) =
      (p i - q i) * pbMassOn (midpointParameters p q) (univ.erase i) k +
      (p j - q j) * pbMassOn (midpointParameters p q) (univ.erase j) k := by
  let s := (univ.erase i).erase j
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hfull : insert i (insert j s) = univ := by
    ext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;> simp_all [s]
  have hsi : insert i s = univ.erase j := by
    ext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;> simp_all [s]
  have hsj : insert j s = univ.erase i := by
    ext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;> simp_all [s]
  have hs : ∀ l ∈ s, p l = q l := by
    intro l hl
    have hl' := mem_erase.mp hl
    exact heq l (mem_erase.mp hl'.2).1 hl'.1
  have ht := pbTailOn_two_coordinate_midpoint p q hi hj hij hs k
  rw [hfull, hsi, hsj] at ht
  exact ht

/-- The one-gap identity, with its deletion law evaluated at the midpoint. -/
theorem tailDiff_one_coordinate_midpoint (p q : Fin n → ℝ) (i : Fin n)
    (heq : ∀ l, l ≠ i → p l = q l) (k : ℕ) :
    tailDiff p q (k + 1) =
      (p i - q i) * pbMassOn (midpointParameters p q) (univ.erase i) k := by
  have hp : Function.update q i (p i) = p := by
    funext l
    by_cases hl : l = i
    · subst l; simp
    · simpa [Function.update_of_ne hl] using (heq l hl).symm
  have hr : ∀ l ∈ univ.erase i, q l = midpointParameters p q l := by
    intro l hl
    simp only [midpointParameters, heq l (mem_erase.mp hl).1]
    ring
  have ht := pbTail_update_sub q i (q i) (p i) k
  rw [hp, Function.update_eq_self, pbMassOn_congr hr] at ht
  exact ht

private theorem two_gap_cases {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (hcard : (positiveGapCoordinates p q).card ≤ 2) (hgap : 0 < meanGap p q) :
    (∃ i, ∀ l, l ≠ i → p l = q l) ∨
      (∃ i j, i ≠ j ∧ ∀ l, l ≠ i → l ≠ j → p l = q l) := by
  obtain ⟨i, hi⟩ := exists_strict_coordinate_of_meanGap_pos h hgap
  by_cases hsecond : ∃ j, j ≠ i ∧ q j < p j
  · obtain ⟨j, hji, hj⟩ := hsecond
    right
    refine ⟨i, j, hji.symm, ?_⟩
    intro l hli hlj
    apply le_antisymm _ (h.2.2 l)
    by_contra hnot
    have hl : q l < p l := lt_of_not_ge hnot
    have hs : ({i, j, l} : Finset (Fin n)) ⊆ positiveGapCoordinates p q := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp [positiveGapCoordinates, hi, hj, hl]
    have hthree : ({i, j, l} : Finset (Fin n)).card = 3 := by
      simp [hji.symm, hli.symm, hlj.symm]
    have hc := card_le_card hs
    rw [hthree] at hc
    omega
  · left
    refine ⟨i, ?_⟩
    intro l hli
    exact le_antisymm (le_of_not_gt (fun hl ↦ hsecond ⟨l, hli, hl⟩)) (h.2.2 l)

/-- The exact symmetric midpoint expansion when at most two coordinate gaps are
positive. Its zero-gap case is included without division. -/
theorem tailDiff_eq_midpoint_deletion_sum {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (hcard : (positiveGapCoordinates p q).card ≤ 2) (k : ℕ) :
    tailDiff p q (k + 1) =
      ∑ i, (p i - q i) * pbMassOn (midpointParameters p q) (univ.erase i) k := by
  by_cases hz : meanGap p q = 0
  · have heq := (meanGap_eq_zero_iff h).mp hz
    subst p
    simp [tailDiff]
  · have hgap : 0 < meanGap p q := lt_of_le_of_ne (meanGap_nonneg h) (Ne.symm hz)
    rcases two_gap_cases h hcard hgap with ⟨i, heq⟩ | ⟨i, j, hij, heq⟩
    · rw [tailDiff_one_coordinate_midpoint p q i heq]
      symm
      apply sum_eq_single i
      · intro l _ hli
        rw [heq l hli, sub_self, zero_mul]
      · intro hi
        exact False.elim (hi (mem_univ i))
    · rw [tailDiff_two_coordinate_midpoint p q hij heq]
      symm
      exact sum_eq_two hij (fun l hli hlj ↦ by rw [heq l hli hlj, sub_self, zero_mul])

/-- The manuscript's normalized midpoint deletion-mixture identity. At zero gap
both sides are zero by Lean's total division convention. -/
theorem tailDiff_div_meanGap_eq_deletionMixture {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hcard : (positiveGapCoordinates p q).card ≤ 2) (k : ℕ) :
    tailDiff p q (k + 1) / meanGap p q =
      deletionMixture (midpointParameters p q) (gapWeights p q) k := by
  rw [tailDiff_eq_midpoint_deletion_sum h hcard]
  simp only [deletionMixture, gapWeights, div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro i _
  ring

/-- With positive total gap and at most two positive coordinate gaps, the
normalized tail differences are exactly one deleted-coordinate Bernoulli law. -/
theorem exists_deleted_law_of_two_gaps {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (hcard : (positiveGapCoordinates p q).card ≤ 2) (hgap : 0 < meanGap p q) :
    ∃ (r : Fin n → ℝ) (i : Fin n), ValidParameters r ∧
      ∀ k, tailDiff p q (k + 1) / meanGap p q = pbMassOn r (univ.erase i) k := by
  have hr := midpointParameters_valid h.1 h.2.1
  rcases two_gap_cases h hcard hgap with ⟨i, heq⟩ | ⟨i, j, hij, heq⟩
  · refine ⟨midpointParameters p q, i, hr, ?_⟩
    have hmean : meanGap p q = p i - q i := by
      rw [meanGap_eq_sum]
      apply sum_eq_single i
      · intro l _ hli
        rw [heq l hli, sub_self]
      · intro hi
        exact False.elim (hi (mem_univ i))
    intro k
    apply (div_eq_iff hgap.ne').mpr
    rw [tailDiff_one_coordinate_midpoint p q i heq, hmean]
    ring
  · let u := (p i - q i) / meanGap p q
    let v := (p j - q j) / meanGap p q
    have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr (h.2.2 i)) hgap.le
    have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr (h.2.2 j)) hgap.le
    have hmean : meanGap p q = (p i - q i) + (p j - q j) := by
      rw [meanGap_eq_sum]
      exact sum_eq_two hij (fun l hli hlj ↦ by rw [heq l hli hlj, sub_self])
    have huv : u + v = 1 := by
      change (p i - q i) / meanGap p q + (p j - q j) / meanGap p q = 1
      rw [← add_div, ← hmean, div_self hgap.ne']
    let r := midpointParameters p q
    let t := Function.update r j (u * r j + v * r i)
    refine ⟨t, i, two_deletion_mixture_valid hr i j hu hv huv, ?_⟩
    let s := (univ.erase i).erase j
    have hi : i ∉ s := by simp [s]
    have hj : j ∉ s := by simp [s]
    have hsi : insert i s = univ.erase j := by
      ext l
      by_cases hli : l = i <;> by_cases hlj : l = j <;> simp_all [s]
    have hsj : insert j s = univ.erase i := by
      ext l
      by_cases hli : l = i <;> by_cases hlj : l = j <;> simp_all [s]
    intro k
    have hmix := pbMassOn_two_deletion_mixture r hi hj u v huv k
    rw [hsi, hsj] at hmix
    rw [← hmix, tailDiff_two_coordinate_midpoint p q hij heq]
    change _ = (p i - q i) / meanGap p q * _ + (p j - q j) / meanGap p q * _
    ring

/-- Relabelling the deleted-coordinate law gives literally `n - 1` Bernoulli
trials, with the subset-sum representation preserved. -/
theorem exists_bernoulli_law_of_two_gaps {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (hcard : (positiveGapCoordinates p q).card ≤ 2) (hgap : 0 < meanGap p q) :
    ∃ r : Fin (n - 1) → ℝ, ValidParameters r ∧
      ∀ k, tailDiff p q (k + 1) / meanGap p q = pbMass r k := by
  obtain ⟨r, i, hr, heq⟩ := exists_deleted_law_of_two_gaps h hcard hgap
  have hsize : (univ.erase i : Finset (Fin n)).card = n - 1 := by simp
  have hex : ∃ t : Fin (univ.erase i : Finset (Fin n)).card → ℝ,
      ValidParameters t ∧ ∀ k, tailDiff p q (k + 1) / meanGap p q = pbMass t k := by
    refine ⟨finsetParameters r (univ.erase i),
      valid_finsetParameters _ (fun j _ ↦ hr j), ?_⟩
    intro k
    rw [pbMass_finsetParameters]
    exact heq k
  rw [hsize] at hex
  exact hex

/-- The midpoint deletion mixture itself is an `(n - 1)`-trial Bernoulli law. -/
theorem deletionMixture_is_bernoulli_of_two_gaps {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hcard : (positiveGapCoordinates p q).card ≤ 2)
    (hgap : 0 < meanGap p q) :
    ∃ r : Fin (n - 1) → ℝ, ValidParameters r ∧
      ∀ k, deletionMixture (midpointParameters p q) (gapWeights p q) k = pbMass r k := by
  obtain ⟨r, hr, heq⟩ := exists_bernoulli_law_of_two_gaps h hcard hgap
  refine ⟨r, hr, ?_⟩
  intro k
  rw [← tailDiff_div_meanGap_eq_deletionMixture h hcard]
  exact heq k

/-- A maximal-atom lower bound for `(n - 1)`-trial Bernoulli sums implies the
manuscript's two-gap bound, including zero total gap. -/
theorem two_gap_lower_bound_of_maximal_atom {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hcard : (positiveGapCoordinates p q).card ≤ 2)
    (κ : ℝ) (hAtom : ∀ r : Fin (n - 1) → ℝ, ValidParameters r →
      ∃ k, k < n ∧ κ ≤ pbMass r k) :
    κ * meanGap p q ≤ tailObjective p q := by
  by_cases hz : meanGap p q = 0
  · rw [tailObjective_eq_zero_of_meanGap_eq_zero h hz, hz, mul_zero]
  · have hgap : 0 < meanGap p q := lt_of_le_of_ne (meanGap_nonneg h) (Ne.symm hz)
    obtain ⟨r, hr, heq⟩ := exists_bernoulli_law_of_two_gaps h hcard hgap
    obtain ⟨k, hk, hmass⟩ := hAtom r hr
    rw [← heq k] at hmass
    have hscaled := (le_div_iff₀ hgap).mp hmass
    exact hscaled.trans (tailDiff_le_tailObjective p q (mem_Icc.mpr ⟨by omega, by omega⟩))

/-- The manuscript's two-gap estimate `T(p,q) ≥ κ_n Δ`, with one-gap and
zero-gap pairs included. -/
theorem two_gap_lower_bound {p q : Fin n → ℝ} (hn : 1 ≤ n)
    (h : AdmissiblePair p q) (hcard : (positiveGapCoordinates p q).card ≤ 2) :
    kappa n * meanGap p q ≤ tailObjective p q := by
  apply two_gap_lower_bound_of_maximal_atom h hcard (kappa n)
  intro r hr
  obtain ⟨k, hk, hmass⟩ := exists_pbMass_ge_kappa n hn hr
  exact ⟨k, by omega, hmass⟩

end

end PoissonBinomialComparison
