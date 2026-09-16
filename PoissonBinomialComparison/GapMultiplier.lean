import PoissonBinomialComparison.FeasibleDirections
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-!
# The scalar gap multiplier

A unit increase in an upper parameter and a unit decrease in a lower parameter
both increase the mean gap by one. Feasible transfers between these slots order
their objective coefficients. Their finite maximum supplies the gap multiplier,
including when all changing coordinates lie at endpoints.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ}

/-- A slot records whether a gap is opened through the upper or lower parameter. -/
def gapSlotDirection : (Fin n ⊕ Fin n) → (Fin n → ℝ) × (Fin n → ℝ)
  | .inl i => (Pi.single i 1, 0)
  | .inr i => (0, -Pi.single i 1)

/-- The linear objective coefficient in a unit gap-opening slot. -/
def gapSlotCoefficient (P Q : Fin n → ℝ) : (Fin n ⊕ Fin n) → ℝ
  | .inl i => P i
  | .inr i => Q i

/-- A changing slot can always reduce its gap. -/
def gapSlotCanDecrease (p q : Fin n → ℝ) : (Fin n ⊕ Fin n) → Prop
  | .inl i => q i < p i
  | .inr i => q i < p i

/-- A slot can increase its gap unless its corresponding parameter is at its
outer box endpoint. -/
def gapSlotCanIncrease (p q : Fin n → ℝ) : (Fin n ⊕ Fin n) → Prop
  | .inl i => p i < 1
  | .inr i => 0 < q i

private theorem sum_gapSlotDirection (r : Fin n ⊕ Fin n) :
    ∑ i, ((gapSlotDirection r).1 i-(gapSlotDirection r).2 i) = 1 := by
  cases r <;> simp [gapSlotDirection]

private theorem gapSlotDirection_signs_increase {p q : Fin n → ℝ}
    (r : Fin n ⊕ Fin n) (hr : gapSlotCanIncrease p q r) (i : Fin n) :
    (p i = 1 → (gapSlotDirection r).1 i ≤ 0) ∧
    (q i = 0 → 0 ≤ (gapSlotDirection r).2 i) ∧
    (p i = q i → (gapSlotDirection r).2 i ≤ (gapSlotDirection r).1 i) := by
  cases r with
  | inl j =>
    change p j < 1 at hr
    by_cases hij : i = j
    · subst i
      simp only [gapSlotDirection, Pi.single_eq_same, Pi.zero_apply]
      exact ⟨by intro h; linarith, by simp, by norm_num⟩
    · simp [gapSlotDirection, Pi.single_eq_of_ne hij]
  | inr j =>
    change 0 < q j at hr
    by_cases hij : i = j
    · subst i
      simp only [gapSlotDirection, Pi.single_eq_same, Pi.zero_apply, Pi.neg_apply]
      exact ⟨by simp, by intro h; linarith, by norm_num⟩
    · simp [gapSlotDirection, Pi.single_eq_of_ne hij]

private theorem gapSlotDirection_signs_decrease {p q : Fin n → ℝ}
    (r : Fin n ⊕ Fin n) (hr : gapSlotCanDecrease p q r) (i : Fin n) :
    (p i = 1 → 0 ≤ (gapSlotDirection r).1 i) ∧
    (q i = 0 → (gapSlotDirection r).2 i ≤ 0) ∧
    (p i = q i → (gapSlotDirection r).1 i ≤ (gapSlotDirection r).2 i) := by
  cases r with
  | inl j =>
    change q j < p j at hr
    by_cases hij : i = j
    · subst i
      simp only [gapSlotDirection, Pi.single_eq_same, Pi.zero_apply]
      exact ⟨by norm_num, by simp, by intro h; linarith⟩
    · simp [gapSlotDirection, Pi.single_eq_of_ne hij]
  | inr j =>
    change q j < p j at hr
    by_cases hij : i = j
    · subst i
      simp only [gapSlotDirection, Pi.single_eq_same, Pi.zero_apply, Pi.neg_apply]
      exact ⟨by simp, by norm_num, by intro h; linarith⟩
    · simp [gapSlotDirection, Pi.single_eq_of_ne hij]

/-- Transfer of one unit of gap from a changing slot to any openable slot. -/
theorem gapSlot_transfer_mem {p q : Fin n → ℝ} {r s : Fin n ⊕ Fin n}
    (hr : gapSlotCanDecrease p q r) (hs : gapSlotCanIncrease p q s) :
    gapSlotDirection s-gapSlotDirection r ∈ feasibleDirections p q := by
  constructor
  · change ∑ i, ((gapSlotDirection s).1 i-(gapSlotDirection r).1 i-
      ((gapSlotDirection s).2 i-(gapSlotDirection r).2 i)) = 0
    simp_rw [show ∀ i, (gapSlotDirection s).1 i-(gapSlotDirection r).1 i-
      ((gapSlotDirection s).2 i-(gapSlotDirection r).2 i) =
      ((gapSlotDirection s).1 i-(gapSlotDirection s).2 i)-
      ((gapSlotDirection r).1 i-(gapSlotDirection r).2 i) by intro i; ring]
    rw [sum_sub_distrib, sum_gapSlotDirection, sum_gapSlotDirection, sub_self]
  · intro i
    have ha := gapSlotDirection_signs_increase s hs i
    have hb := gapSlotDirection_signs_decrease r hr i
    change (p i = 1 → (gapSlotDirection s).1 i-(gapSlotDirection r).1 i ≤ 0) ∧
      (q i = 0 → 0 ≤ (gapSlotDirection s).2 i-(gapSlotDirection r).2 i) ∧
      (p i = q i → (gapSlotDirection s).2 i-(gapSlotDirection r).2 i ≤
        (gapSlotDirection s).1 i-(gapSlotDirection r).1 i)
    exact ⟨fun h ↦ sub_nonpos.mpr ((ha.1 h).trans (hb.1 h)),
      fun h ↦ sub_nonneg.mpr ((hb.2.1 h).trans (ha.2.1 h)),
      fun h ↦ sub_le_sub (ha.2.2 h) (hb.2.2 h)⟩

private theorem gapSlotCoefficient_eq_sum (P Q : Fin n → ℝ) (r : Fin n ⊕ Fin n) :
    (∑ i, ((gapSlotDirection r).1 i*P i-(gapSlotDirection r).2 i*Q i)) =
      gapSlotCoefficient P Q r := by
  cases r <;> simp [gapSlotDirection, gapSlotCoefficient, Pi.single_apply, ite_mul]

/-- Necessary first-order inequalities order closing and opening coefficients. -/
theorem gapSlotCoefficient_le {p q P Q : Fin n → ℝ}
    (hstat : ∀ d ∈ feasibleDirections p q, 0 ≤ ∑ i, (d.1 i*P i-d.2 i*Q i))
    {r s : Fin n ⊕ Fin n} (hr : gapSlotCanDecrease p q r) (hs : gapSlotCanIncrease p q s) :
    gapSlotCoefficient P Q r ≤ gapSlotCoefficient P Q s := by
  have h := hstat _ (gapSlot_transfer_mem hr hs)
  change 0 ≤ ∑ i, (((gapSlotDirection s).1 i-(gapSlotDirection r).1 i)*P i-
    ((gapSlotDirection s).2 i-(gapSlotDirection r).2 i)*Q i) at h
  simp_rw [show ∀ i, ((gapSlotDirection s).1 i-(gapSlotDirection r).1 i)*P i-
      ((gapSlotDirection s).2 i-(gapSlotDirection r).2 i)*Q i =
      ((gapSlotDirection s).1 i*P i-(gapSlotDirection s).2 i*Q i)-
      ((gapSlotDirection r).1 i*P i-(gapSlotDirection r).2 i*Q i) by intro i; ring] at h
  rw [sum_sub_distrib, gapSlotCoefficient_eq_sum, gapSlotCoefficient_eq_sum] at h
  exact sub_nonneg.mp h

/-- The gap multiplier exists even if there are no free changing parameters. -/
theorem exists_gap_multiplier {p q P Q : Fin n → ℝ} (hchange : ∃ i, q i < p i)
    (hstat : ∀ d ∈ feasibleDirections p q, 0 ≤ ∑ i, (d.1 i*P i-d.2 i*Q i)) :
    ∃ c : ℝ, (∀ r, gapSlotCanDecrease p q r → gapSlotCoefficient P Q r ≤ c) ∧
      (∀ s, gapSlotCanIncrease p q s → c ≤ gapSlotCoefficient P Q s) := by
  classical
  let L := univ.filter (gapSlotCanDecrease p q)
  have hne : L.Nonempty := by
    obtain ⟨i,hi⟩ := hchange
    exact ⟨Sum.inl i, mem_filter.mpr ⟨mem_univ _,hi⟩⟩
  refine ⟨L.sup' hne (gapSlotCoefficient P Q), ?_, ?_⟩
  · intro r hr
    exact le_sup' _ (mem_filter.mpr ⟨mem_univ _,hr⟩)
  · intro s hs
    apply sup'_le
    intro r hr
    exact gapSlotCoefficient_le hstat (mem_filter.mp hr).2 hs

/-- A common interior coordinate is free to move jointly in either direction. -/
theorem common_coordinate_gradient_eq {p q P Q : Fin n → ℝ}
    (hstat : ∀ d ∈ feasibleDirections p q, 0 ≤ ∑ i, (d.1 i*P i-d.2 i*Q i))
    (i : Fin n) (hp : p i < 1) (hq : 0 < q i) : P i = Q i := by
  have hdir (t : ℝ) : ((Pi.single i t), (Pi.single i t)) ∈ feasibleDirections p q := by
    constructor
    · simp
    · intro j
      by_cases hji : j = i
      · subst j
        simp only [Pi.single_eq_same]
        exact ⟨by intro h; linarith, by intro h; linarith, by simp⟩
      · simp [Pi.single_eq_of_ne hji]
  have hpos := hstat _ (hdir 1)
  have hneg := hstat _ (hdir (-1))
  simp [Pi.single_apply, ite_mul, sum_sub_distrib] at hpos hneg
  linarith

/-- Coordinate form of the manuscript's gap multiplier conditions. At a common
interior coordinate, its common gradient is `c` plus a nonnegative multiplier. -/
theorem exists_gap_multiplier_coordinates {p q P Q : Fin n → ℝ}
    (hchange : ∃ i, q i < p i)
    (hcommon : ∀ i, p i = q i → 0 < q i ∧ p i < 1)
    (hstat : ∀ d ∈ feasibleDirections p q, 0 ≤ ∑ i, (d.1 i*P i-d.2 i*Q i)) :
    ∃ c : ℝ,
      (∀ i, q i < p i → P i ≤ c ∧ Q i ≤ c ∧
        (p i < 1 → P i = c) ∧ (0 < q i → Q i = c)) ∧
      (∀ i, p i = q i → ∃ ν : ℝ, 0 ≤ ν ∧ P i = c+ν ∧ Q i = c+ν) := by
  obtain ⟨c,hclose,hopen⟩ := exists_gap_multiplier hchange hstat
  refine ⟨c,?_,?_⟩
  · intro i hi
    have hp := hclose (Sum.inl i) hi
    have hq := hclose (Sum.inr i) hi
    exact ⟨hp,hq, fun h ↦ le_antisymm hp (hopen (Sum.inl i) h),
      fun h ↦ le_antisymm hq (hopen (Sum.inr i) h)⟩
  · intro i hi
    obtain ⟨hq,hp⟩ := hcommon i hi
    have heq := common_coordinate_gradient_eq hstat i hp hq
    have hc := hopen (Sum.inl i) hp
    refine ⟨P i-c, sub_nonneg.mpr hc, by ring, ?_⟩
    linarith

end

end PoissonBinomialComparison
