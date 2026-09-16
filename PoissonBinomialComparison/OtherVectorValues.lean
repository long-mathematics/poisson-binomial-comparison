import PoissonBinomialComparison.OneVectorConstant

/-!
# The positive values of the other changing vector

The randomized deletion masses are extended to integer counts so that the
three-count argument also covers thresholds one and two. Three distinct free
parameter values would force three consecutive positive masses to be equal,
contradicting strict log-concavity.
-/

namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Integer-count law after adjoining the randomizing Bernoulli variable. -/
def randomizedMassIntOn (p : ι → ℝ) (s : Finset ι) (w : ℝ) (k : ℤ) : ℝ :=
  bernoulliConvolve (pbMassIntOn p s) w k

/-- The integer formulation agrees with the existing randomized slope at all
natural counts. -/
@[simp] theorem randomizedMassIntOn_natCast (p : ι → ℝ) (s : Finset ι) (w : ℝ) (k : ℕ) :
    randomizedMassIntOn p s w k = randomizedSlopeOn p s w k := by
  cases k with
  | zero => simp [randomizedMassIntOn, bernoulliConvolve, randomizedSlopeOn, pbMassIntOn]
  | succ k =>
    have heq : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
    simp only [randomizedMassIntOn, bernoulliConvolve, heq, pbMassIntOn_natCast,
      randomizedSlopeOn, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]

/-- Negative integer counts have zero randomized mass. -/
theorem randomizedMassIntOn_of_neg (p : ι → ℝ) (s : Finset ι) (w : ℝ)
    {k : ℤ} (hk : k < 0) : randomizedMassIntOn p s w k = 0 := by
  simp [randomizedMassIntOn, bernoulliConvolve, pbMassIntOn_of_neg p s hk,
    pbMassIntOn_of_neg p s (by omega : k - 1 < 0)]

/-- The randomized law obeys the usual Bernoulli insertion recurrence. -/
theorem randomizedMassIntOn_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (w : ℝ) (k : ℤ) :
    randomizedMassIntOn p (insert i s) w k =
      (1 - p i) * randomizedMassIntOn p s w k +
        p i * randomizedMassIntOn p s w (k - 1) := by
  simp only [randomizedMassIntOn, bernoulliConvolve, pbMassIntOn_insert p hi]
  ring

/-- The integer randomized masses are nonnegative. -/
theorem randomizedMassIntOn_nonneg {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (k : ℤ) : 0 ≤ randomizedMassIntOn p s w k :=
  bernoulliConvolve_nonneg (pbMassIntOn_nonneg hp) hw0 hw1 k

/-- Cross inequalities also hold for the integer randomized masses. -/
theorem randomizedMassIntOn_cross {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    MassCrossInequalities (randomizedMassIntOn p s w) :=
  (pbMassIntOn_cross s hp).convolve hw0 (sub_nonneg.mpr hw1)

/-- Strict log-concavity includes deterministic randomizing variables. -/
theorem randomizedMassIntOn_strictLogConcavity {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    StrictMassLogConcavity (randomizedMassIntOn p s w) :=
  StrictMassLogConcavity.convolve (pbMassIntOn_nonneg hp) (pbMassIntOn_cross s hp)
    (pbMassIntOn_strictLogConcavity s hp) hw0 (sub_nonneg.mpr hw1)

/-- The mixed coefficient is the difference of two consecutive randomized
integer-count masses, including the zero-count convention. -/
theorem randomizedCoefficientOn_eq_int (p : ι → ℝ) (s : Finset ι) (w : ℝ) (k : ℕ) :
    randomizedCoefficientOn p s w k =
      randomizedMassIntOn p s w ((k : ℤ) - 1) - randomizedMassIntOn p s w k := by
  cases k with
  | zero =>
    have hz : randomizedMassIntOn p s w (0 : ℤ) = randomizedSlopeOn p s w 0 :=
      randomizedMassIntOn_natCast p s w 0
    simp [randomizedCoefficientOn, randomizedMassIntOn_of_neg, hz]
  | succ k =>
    have heq : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
    simp only [randomizedCoefficientOn, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
      heq, randomizedMassIntOn_natCast]

variable {n : ℕ} {q : Fin n → ℝ}

/-- Three distinct parameter values cannot all have the same positive free
gradient (QTWO). -/
theorem not_three_distinct_of_equal_positive_gradients (hq : ValidParameters q)
    {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c)
    (k : ℕ) {i j l : Fin n} (hijq : q i ≠ q j) (hilq : q i ≠ q l) (hjlq : q j ≠ q l)
    (hGi : randomizedGradient q w k i = c)
    (hGj : randomizedGradient q w k j = c)
    (hGl : randomizedGradient q w k l = c) : False := by
  have hij : i ≠ j := fun heq ↦ hijq (congrArg q heq)
  have hil : i ≠ l := fun heq ↦ hilq (congrArg q heq)
  have hjl : j ≠ l := fun heq ↦ hjlq (congrArg q heq)
  have hCij : randomizedMixedCoefficient q w k i j = 0 := by
    have hd := randomizedGradient_sub q hij w k
    rw [hGi, hGj, sub_self] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (sub_ne_zero.mpr hijq.symm)
  have hCil : randomizedMixedCoefficient q w k i l = 0 := by
    have hd := randomizedGradient_sub q hil w k
    rw [hGi, hGl, sub_self] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (sub_ne_zero.mpr hilq.symm)
  let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
  have hj : j ∉ s := by simp [s]
  have hl : l ∉ s := by simp [s]
  have hsij : insert l s = (univ.erase i).erase j := by
    apply insert_erase
    simp [hil.symm, hjl.symm]
  have hsil : insert j s = (univ.erase i).erase l := by
    ext t
    by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l <;>
      simp_all [s]
  have hsi : insert j (insert l s) = univ.erase i := by
    rw [hsij]
    apply insert_erase
    simp [hij.symm]
  let X := randomizedMassIntOn q s w ((k : ℤ) - 2)
  let Y := randomizedMassIntOn q s w ((k : ℤ) - 1)
  let Z := randomizedMassIntOn q s w k
  have heq (t : Fin n) (ht : t ∉ s) :
      randomizedCoefficientOn q (insert t s) w k =
        (1 - q t) * (Y - Z) + q t * (X - Y) := by
    rw [randomizedCoefficientOn_eq_int, randomizedMassIntOn_insert q ht,
      randomizedMassIntOn_insert q ht]
    dsimp [X, Y, Z]
    rw [show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 by omega]
    ring
  have hlzero : (1 - q l) * (Y - Z) + q l * (X - Y) = 0 := by
    rw [← heq l hl, hsij]
    exact hCij
  have hjzero : (1 - q j) * (Y - Z) + q j * (X - Y) = 0 := by
    rw [← heq j hj, hsil]
    exact hCil
  have hab : X - Y = Y - Z := by
    have hh : (q j - q l) * ((X - Y) - (Y - Z)) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hjlq))
  rw [hab] at hjzero
  have hYZ : Y = Z := by nlinarith [hjzero]
  have hXY : X = Y := by linarith
  have hgrad : randomizedGradient q w k i = Y := by
    change randomizedSlopeOn q (univ.erase i) w k = Y
    rw [← randomizedMassIntOn_natCast, ← hsi,
      randomizedMassIntOn_insert q (by simp [hjl, hj]),
      randomizedMassIntOn_insert q hl, randomizedMassIntOn_insert q hl]
    change (1 - q j) * ((1 - q l) * Z + q l * Y) +
      q j * ((1 - q l) * Y + q l * randomizedMassIntOn q s w ((k : ℤ) - 1 - 1)) = Y
    rw [show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 by omega]
    change (1 - q j) * ((1 - q l) * Z + q l * Y) +
      q j * ((1 - q l) * Y + q l * X) = Y
    rw [hXY, ← hYZ]
    ring
  have hY : 0 < Y := by linarith
  have hLC := randomizedMassIntOn_strictLogConcavity s (fun t _ ↦ hq t) hw0 hw1
    ((k : ℤ) - 1) hY
  have hcast : (k : ℤ) - 1 + 1 = (k : ℤ) := by omega
  have hcast' : (k : ℤ) - 1 - 1 = (k : ℤ) - 2 := by omega
  change randomizedMassIntOn q s w ((k : ℤ) - 1 - 1) *
    randomizedMassIntOn q s w ((k : ℤ) - 1 + 1) < Y ^ 2 at hLC
  rw [hcast, hcast'] at hLC
  change X * Z < Y ^ 2 at hLC
  rw [hXY, ← hYZ] at hLC
  nlinarith

/-- At most two distinct values occur on a set of coordinates whose gradients
are all equal to the same positive multiplier. In particular this applies to
the positive lower changing coordinates under KKT. -/
theorem card_values_le_two_of_equal_positive_gradients (hq : ValidParameters q)
    {I : Finset (Fin n)} {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c)
    (k : ℕ) (hgrad : ∀ i ∈ I, randomizedGradient q w k i = c) :
    (I.image q).card ≤ 2 := by
  classical
  by_contra hnot
  obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := two_lt_card.mp (lt_of_not_ge hnot)
  obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hd
  exact not_three_distinct_of_equal_positive_gradients hq hw0 hw1 hc k hab had hbd
    (hgrad i hi) (hgrad j hj) (hgrad l hl)

end

end PoissonBinomialComparison
