import PoissonBinomialComparison.TotalVariation

/-!
# The two-dimensional equality classification

This module develops the explicit tail and product total variation formulas
in the manuscript's appendix. Coordinates `0, 1` correspond to its `1, 2`.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

theorem tailObjective_two_eq_abs (p q : Fin 2 → ℝ) :
    tailObjective p q = meanGap p q / 2 +
      |p 0 * p 1 - q 0 * q 1 - meanGap p q / 2| := by
  have htwo : tailDiff p q 2 = p 0 * p 1 - q 0 * q 1 := by
    simp [tailDiff, pbTail_two_two]
  have hone : tailDiff p q 1 = meanGap p q - (p 0 * p 1 - q 0 * q 1) := by
    have hsum := tailDiff_one_add_two p q
    rw [htwo] at hsum
    linarith
  rw [tailObjective_two, hone, htwo]
  rcases le_total (meanGap p q / 2) (p 0 * p 1 - q 0 * q 1) with h | h
  · rw [max_eq_right (by linarith), abs_of_nonneg (by linarith)]
    ring
  · rw [max_eq_left (by linarith), abs_of_nonpos (by linarith)]
    ring

theorem tailObjective_two_eq_half_iff (p q : Fin 2 → ℝ) :
    tailObjective p q = meanGap p q / 2 ↔
      p 0 * p 1 - q 0 * q 1 = meanGap p q / 2 := by
  rw [tailObjective_two_eq_abs]
  constructor
  · intro h
    have hz : |p 0 * p 1 - q 0 * q 1 - meanGap p q / 2| = 0 := by linarith
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  · intro h
    simp [h]

theorem twoTopGap_bounds {p q : Fin 2 → ℝ} (h : AdmissiblePair p q) :
    0 ≤ p 0 * p 1 - q 0 * q 1 ∧
      p 0 * p 1 - q 0 * q 1 ≤ meanGap p q := by
  have h0 := (admissiblePair_iff p q).mp h 0
  have h1 := (admissiblePair_iff p q).mp h 1
  constructor
  · exact sub_nonneg.mpr (mul_le_mul h0.2.1 h1.2.1 h1.1 (h0.1.trans h0.2.1))
  · simp only [meanGap, Fin.sum_univ_two]
    have ha := mul_nonneg (sub_nonneg.mpr h0.2.1) (sub_nonneg.mpr h1.2.2)
    have hb := mul_nonneg (sub_nonneg.mpr h1.2.1)
      (sub_nonneg.mpr (h0.2.1.trans h0.2.2))
    nlinarith

private theorem productTV_two_atoms (p q : Fin 2 → ℝ) :
    productTV p q =
      (|p 0 * p 1 - q 0 * q 1 - meanGap p q| +
        |p 0 - q 0 - (p 0 * p 1 - q 0 * q 1)| +
        |p 1 - q 1 - (p 0 * p 1 - q 0 * q 1)| +
        |p 0 * p 1 - q 0 * q 1|) / 2 := by
  have h : (univ : Finset (Fin 2)).powerset = {∅, {0}, {1}, {0, 1}} := by decide
  rw [productTV, h]
  rw [sum_insert (by decide : (∅ : Finset (Fin 2)) ∉ ({ {0}, {1}, {0, 1} } : Finset (Finset (Fin 2))))]
  rw [sum_insert (by decide : ({0} : Finset (Fin 2)) ∉ ({ {1}, {0, 1} } : Finset (Finset (Fin 2))))]
  rw [sum_insert (by decide : ({1} : Finset (Fin 2)) ∉ ({ {0, 1} } : Finset (Finset (Fin 2))))]
  have hs : ({0, 1} : Finset (Fin 2)) \ {0} = {1} := by decide
  simp [bernoulliWeight, Finset.univ_fin2, meanGap, hs]
  ring_nf

theorem productTV_two_eq_abs {p q : Fin 2 → ℝ} (h : AdmissiblePair p q) :
    productTV p q = meanGap p q / 2 +
      (|p 0 - q 0 - (p 0 * p 1 - q 0 * q 1)| +
       |p 1 - q 1 - (p 0 * p 1 - q 0 * q 1)|) / 2 := by
  have hb := twoTopGap_bounds h
  rw [productTV_two_atoms, abs_of_nonpos (sub_nonpos.mpr hb.2), abs_of_nonneg hb.1]
  ring

/-- The product equality condition, before choosing a family parameter. -/
theorem productTV_two_eq_half_iff {p q : Fin 2 → ℝ} (h : AdmissiblePair p q) :
    productTV p q = meanGap p q / 2 ↔
      p 0 - q 0 = meanGap p q / 2 ∧
      p 1 - q 1 = meanGap p q / 2 ∧
      p 0 * p 1 - q 0 * q 1 = meanGap p q / 2 := by
  have hsum : (p 0 - q 0) + (p 1 - q 1) = meanGap p q := by
    simp [meanGap, Fin.sum_univ_two]
    ring
  rw [productTV_two_eq_abs h]
  constructor
  · intro he
    have h0 := abs_nonneg (p 0 - q 0 - (p 0 * p 1 - q 0 * q 1))
    have h1 := abs_nonneg (p 1 - q 1 - (p 0 * p 1 - q 0 * q 1))
    have e0 : p 0 - q 0 = p 0 * p 1 - q 0 * q 1 :=
      sub_eq_zero.mp (abs_eq_zero.mp (by linarith))
    have e1 : p 1 - q 1 = p 0 * p 1 - q 0 * q 1 :=
      sub_eq_zero.mp (abs_eq_zero.mp (by linarith))
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, ha⟩
    rw [h0, h1, ha]
    simp

/-- The exact one-parameter product-minimizing family in the appendix. -/
theorem productTV_two_eq_half_iff_family {p q : Fin 2 → ℝ}
    (h : AdmissiblePair p q) (hgap : 0 < meanGap p q) :
    productTV p q = meanGap p q / 2 ↔
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 - meanGap p q / 2 ∧
        p 0 = r + meanGap p q / 2 ∧ p 1 = 1 - r ∧
        q 0 = r ∧ q 1 = 1 - meanGap p q / 2 - r := by
  rw [productTV_two_eq_half_iff h]
  constructor
  · rintro ⟨h0, h1, ha⟩
    have hqsum : q 0 + q 1 + meanGap p q / 2 = 1 := by
      have he : meanGap p q / 2 * (q 0 + q 1 + meanGap p q / 2 - 1) = 0 := by
        have hp0 : p 0 = q 0 + meanGap p q / 2 := by linarith
        have hp1 : p 1 = q 1 + meanGap p q / 2 := by linarith
        rw [hp0, hp1] at ha
        nlinarith [ha]
      have := (mul_eq_zero.mp he).resolve_left (ne_of_gt (by linarith))
      linarith
    have hp0 := (admissiblePair_iff p q).mp h 0
    refine ⟨q 0, hp0.1, ?_, ?_, ?_, rfl, ?_⟩ <;> linarith
  · rintro ⟨r, _, _, hp0, hp1, hq0, hq1⟩
    exact ⟨by linarith, by linarith, by rw [hp0, hp1, hq0, hq1]; ring⟩

/-- The feasibility interval in the displayed family is exact. -/
theorem twoFamily_admissible_iff (d r : ℝ) :
    AdmissiblePair (fun i : Fin 2 ↦ if i = 0 then r + d else 1 - r)
      (fun i ↦ if i = 0 then r else 1 - d - r) ↔
      0 ≤ d ∧ 0 ≤ r ∧ r ≤ 1 - d := by
  rw [admissiblePair_iff]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [ite_true] at h0
    norm_num at h1
    exact ⟨by linarith [h0.2.1], h0.1, by linarith [h0.2.2]⟩
  · rintro ⟨hd, hr, hrb⟩ i
    split_ifs <;> exact ⟨by linarith, by linarith, by linarith⟩

/-- Every feasible member of the family has gap `2*d` and minimizes both
objectives; the converse product classification is given above. -/
theorem twoFamily_attains (d r : ℝ) (hd : 0 ≤ d) (hr : 0 ≤ r) (hrb : r ≤ 1 - d) :
    let p : Fin 2 → ℝ := fun i ↦ if i = 0 then r + d else 1 - r
    let q : Fin 2 → ℝ := fun i ↦ if i = 0 then r else 1 - d - r
    AdmissiblePair p q ∧ meanGap p q = 2 * d ∧
      tailObjective p q = d ∧ productTV p q = d := by
  let p : Fin 2 → ℝ := fun i ↦ if i = 0 then r + d else 1 - r
  let q : Fin 2 → ℝ := fun i ↦ if i = 0 then r else 1 - d - r
  change AdmissiblePair p q ∧ meanGap p q = 2 * d ∧
    tailObjective p q = d ∧ productTV p q = d
  have hpq : AdmissiblePair p q := (twoFamily_admissible_iff d r).mpr ⟨hd, hr, hrb⟩
  have hg : meanGap p q = 2 * d := by
    simp [p, q, meanGap, Fin.sum_univ_two]
    ring
  have ha : p 0 * p 1 - q 0 * q 1 = d := by
    simp [p, q]
    ring
  refine ⟨hpq, hg, ?_, ?_⟩
  · rw [tailObjective_two_eq_abs, hg, ha]
    simp
  · rw [productTV_two_eq_abs hpq, hg, ha]
    simp [p, q]

/-- Product total variation obeys the same sharp two-dimensional bound. -/
theorem productTV_two_lower_bound (p q : Fin 2 → ℝ) :
    meanGap p q / 2 ≤ productTV p q :=
  (twoDimensional_lower_bound p q).trans (tailObjective_le_productTV p q)

/-- Complementary homogeneous parameters also attain the product minimum. -/
theorem complementaryPair_two_product_attains (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ2 : Δ ≤ 2) :
    let p : Fin 2 → ℝ := fun _ ↦ (1 + Δ / 2) / 2
    let q : Fin 2 → ℝ := fun _ ↦ (1 - Δ / 2) / 2
    AdmissiblePair p q ∧ meanGap p q = Δ ∧ productTV p q = Δ / 2 := by
  have h := complementaryPair_two_attains Δ hΔ0 hΔ2
  dsimp only at h ⊢
  refine ⟨h.1, h.2.1, ?_⟩
  have he := (productTV_two_eq_half_iff h.1).mpr ?_
  · simpa [h.2.1] using he
  · rw [h.2.1]
    constructor
    · ring
    constructor <;> ring

/-- Product minimizers are always tail minimizers. -/
theorem productTV_two_eq_half_implies_tail (p q : Fin 2 → ℝ)
    (h : productTV p q = meanGap p q / 2) :
    tailObjective p q = meanGap p q / 2 :=
  le_antisymm (h ▸ tailObjective_le_productTV p q) (twoDimensional_lower_bound p q)

/-- The appendix's asymmetric complementary pair has an exact positive
separation between the two objectives. -/
theorem asymmetricPair_two_objectives (d ε : ℝ)
    (hε : 0 ≤ ε) (hεd : ε ≤ d) (hε1 : ε ≤ 1 - d) :
    let p : Fin 2 → ℝ := fun i ↦ if i = 0 then (1 + d + ε) / 2 else (1 + d - ε) / 2
    let q : Fin 2 → ℝ := fun i ↦ if i = 0 then (1 - d - ε) / 2 else (1 - d + ε) / 2
    AdmissiblePair p q ∧ meanGap p q = 2 * d ∧
      tailObjective p q = d ∧ productTV p q = d + ε := by
  let p : Fin 2 → ℝ := fun i ↦ if i = 0 then (1 + d + ε) / 2 else (1 + d - ε) / 2
  let q : Fin 2 → ℝ := fun i ↦ if i = 0 then (1 - d - ε) / 2 else (1 - d + ε) / 2
  change AdmissiblePair p q ∧ meanGap p q = 2 * d ∧
    tailObjective p q = d ∧ productTV p q = d + ε
  have hpq : AdmissiblePair p q := by
    rw [admissiblePair_iff]
    intro i
    dsimp [p, q]
    split_ifs <;> exact ⟨by linarith, by linarith, by linarith⟩
  have hg : meanGap p q = 2 * d := by
    simp [meanGap, Fin.sum_univ_two, p, q]
    ring
  have ha : p 0 * p 1 - q 0 * q 1 = d := by
    simp [p, q]
    ring
  have h0 : p 0 - q 0 - d = ε := by simp [p, q]; ring
  have h1 : p 1 - q 1 - d = -ε := by simp [p, q]; ring
  refine ⟨hpq, hg, ?_, ?_⟩
  · rw [tailObjective_two_eq_abs, hg, ha]
    simp
  · rw [productTV_two_eq_abs hpq, hg, ha, h0, h1, abs_neg, abs_of_nonneg hε]
    ring

/-- At every strictly intermediate gap, a tail minimizer exists which is not
a product minimizer. Together with `productTV_two_eq_half_implies_tail`, this
proves the strict containment asserted in the appendix. -/
theorem exists_two_tail_minimizer_not_product (Δ : ℝ) (h0 : 0 < Δ) (h2 : Δ < 2) :
    ∃ p q : Fin 2 → ℝ, AdmissiblePair p q ∧ meanGap p q = Δ ∧
      tailObjective p q = Δ / 2 ∧ Δ / 2 < productTV p q := by
  let d := Δ / 2
  let ε := min d (1 - d) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hd1 : d < 1 := by dsimp [d]; linarith
  have hmin : 0 < min d (1 - d) := lt_min hd (by linarith)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεd : ε ≤ d := by have := min_le_left d (1-d); dsimp [ε]; linarith
  have hε1 : ε ≤ 1 - d := by have := min_le_right d (1-d); dsimp [ε]; linarith
  have h := asymmetricPair_two_objectives d ε hε.le hεd hε1
  dsimp only at h
  refine ⟨_, _, h.1, ?_, h.2.2.1, ?_⟩
  · rw [h.2.1]
    dsimp [d]
    ring
  · rw [h.2.2.2]
    change d < d + ε
    linarith

end

end PoissonBinomialComparison
