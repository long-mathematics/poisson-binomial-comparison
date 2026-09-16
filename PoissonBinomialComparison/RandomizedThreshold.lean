import PoissonBinomialComparison.Coordinate

/-!
# The randomized adjacent-threshold test

`randomizedTailOn p s w k` is the manuscript's convex combination of tails at
`k` and `k + 1`. Its coordinate slope and mixed coefficient are represented by
finite mass formulas. Exact update identities identify these as the coefficients
of the affine and quadratic parameter polynomials, without analytic derivatives.
The separate zero-count conventions express the absent mass at count `-1`.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- The randomized adjacent-threshold test on a finite coordinate set. -/
def randomizedTailOn (p : ι → ℝ) (s : Finset ι) (w : ℝ) (k : ℕ) : ℝ :=
  w * pbTailOn p s k + (1 - w) * pbTailOn p s (k + 1)

/-- The count mass after adjoining the randomizing Bernoulli parameter `w`.
This is the exact coordinate slope of the randomized tail test. -/
def randomizedSlopeOn (p : ι → ℝ) (s : Finset ι) (w : ℝ) (k : ℕ) : ℝ :=
  (1 - w) * pbMassOn p s k + w * (if k = 0 then 0 else pbMassOn p s (k - 1))

/-- The adjacent-mass difference of the randomized deletion law, equal to the
mixed coordinate coefficient of the randomized test. -/
def randomizedCoefficientOn (p : ι → ℝ) (s : Finset ι) (w : ℝ) (k : ℕ) : ℝ :=
  (if k = 0 then 0 else randomizedSlopeOn p s w (k - 1)) - randomizedSlopeOn p s w k

private theorem randomizedTailOn_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (w : ℝ) (k : ℕ) :
    randomizedTailOn p s w k = randomizedTailOn q s w k := by
  simp only [randomizedTailOn, pbTailOn_congr h]

private theorem randomizedSlopeOn_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (w : ℝ) (k : ℕ) :
    randomizedSlopeOn p s w k = randomizedSlopeOn q s w k := by
  simp only [randomizedSlopeOn, pbMassOn_congr h]

private theorem randomizedCoefficientOn_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (w : ℝ) (k : ℕ) :
    randomizedCoefficientOn p s w k = randomizedCoefficientOn q s w k := by
  simp only [randomizedCoefficientOn, randomizedSlopeOn_congr h]

/-- Adjoining the randomizing Bernoulli parameter converts the test to one tail. -/
theorem randomizedTailOn_eq_adjoin (p : ι → ℝ) {s : Finset ι} {e : ι}
    (he : e ∉ s) (w : ℝ) (k : ℕ) :
    randomizedTailOn p s w k =
      pbTailOn (Function.update p e w) (insert e s) (k + 1) := by
  rw [pbTailOn_insert_succ _ he]
  simp only [Function.update_self, pbTailOn_update_of_notMem p he, randomizedTailOn]
  ring

/-- The slope is the mass at count `k` after adjoining the randomizing variable. -/
theorem randomizedSlopeOn_eq_adjoin (p : ι → ℝ) {s : Finset ι} {e : ι}
    (he : e ∉ s) (w : ℝ) (k : ℕ) :
    randomizedSlopeOn p s w k =
      pbMassOn (Function.update p e w) (insert e s) k := by
  cases k with
  | zero =>
    rw [pbMassOn_insert_zero _ he]
    simp [randomizedSlopeOn, pbMassOn_update_of_notMem p he]
  | succ k =>
    rw [pbMassOn_insert_succ _ he]
    simp [randomizedSlopeOn, pbMassOn_update_of_notMem p he]

/-- The mixed coefficient is the difference of adjacent masses after adjoining
 the randomizing Bernoulli variable, exactly as in the manuscript. -/
theorem randomizedCoefficientOn_eq_adjoin (p : ι → ℝ) {s : Finset ι} {e : ι}
    (he : e ∉ s) (w : ℝ) (k : ℕ) :
    randomizedCoefficientOn p s w (k + 1) =
      pbMassOn (Function.update p e w) (insert e s) k -
        pbMassOn (Function.update p e w) (insert e s) (k + 1) := by
  simp only [randomizedCoefficientOn, Nat.add_one_ne_zero, ite_false,
    Nat.add_sub_cancel, randomizedSlopeOn_eq_adjoin p he]

/-- Exact affine dependence on an inserted coordinate. -/
theorem randomizedTailOn_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (w : ℝ) (k : ℕ) :
    randomizedTailOn p (insert i s) w k =
      randomizedTailOn p s w k + p i * randomizedSlopeOn p s w k := by
  cases k with
  | zero =>
    simp only [randomizedTailOn, pbTailOn_zero, pbTailOn_insert_succ p hi,
      randomizedSlopeOn, ite_true, mul_zero, add_zero]
    have h := pbTailOn_sub_succ p s 0
    simp only [pbTailOn_zero] at h
    rw [← h]
    ring
  | succ k =>
    simp only [randomizedTailOn, pbTailOn_insert_succ p hi, randomizedSlopeOn,
      Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [← pbTailOn_sub_succ p s k, ← pbTailOn_sub_succ p s (k + 1)]
    ring

/-- Exact affine dependence of the slope; its coefficient is the mixed derivative. -/
theorem randomizedSlopeOn_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (w : ℝ) (k : ℕ) :
    randomizedSlopeOn p (insert i s) w k =
      randomizedSlopeOn p s w k + p i * randomizedCoefficientOn p s w k := by
  cases k with
  | zero =>
    simp only [randomizedSlopeOn, randomizedCoefficientOn, ite_true, mul_zero,
      add_zero, pbMassOn_insert_zero p hi]
    ring
  | succ k =>
    cases k with
    | zero =>
      simp only [randomizedSlopeOn, randomizedCoefficientOn, Nat.succ_ne_zero,
        ite_false, Nat.add_sub_cancel, ite_true, mul_zero, add_zero,
        pbMassOn_insert_succ p hi, pbMassOn_insert_zero p hi]
      ring
    | succ k =>
      simp only [randomizedSlopeOn, randomizedCoefficientOn, Nat.succ_ne_zero,
        ite_false, Nat.add_sub_cancel, pbMassOn_insert_succ p hi]
      ring

/-- The manuscript's gradient-difference identity on the common double-deletion set. -/
theorem randomizedSlopeOn_insert_sub (p : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (w : ℝ) (k : ℕ) :
    randomizedSlopeOn p (insert j s) w k - randomizedSlopeOn p (insert i s) w k =
      (p j - p i) * randomizedCoefficientOn p s w k := by
  rw [randomizedSlopeOn_insert p hj, randomizedSlopeOn_insert p hi]
  ring

/-- The exact symmetric quadratic polynomial in two inserted coordinates. -/
theorem randomizedTailOn_insert_insert (p : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j) (w : ℝ) (k : ℕ) :
    randomizedTailOn p (insert i (insert j s)) w k =
      randomizedTailOn p s w k + (p i + p j) * randomizedSlopeOn p s w k +
        p i * p j * randomizedCoefficientOn p s w k := by
  rw [randomizedTailOn_insert p (by simp [hi, hij]),
    randomizedTailOn_insert p hj, randomizedSlopeOn_insert p hj]
  ring

/-- Changing one coordinate changes the randomized test by increment times slope. -/
theorem randomizedTailOn_update_sub (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (a b w : ℝ) (k : ℕ) :
    randomizedTailOn (Function.update p i b) (insert i s) w k -
      randomizedTailOn (Function.update p i a) (insert i s) w k =
        (b - a) * randomizedSlopeOn p s w k := by
  have heq (x : ℝ) : ∀ j ∈ s, Function.update p i x j = p j := by
    intro j hj
    have hji : j ≠ i := by
      intro h
      subst j
      exact hi hj
    exact Function.update_of_ne hji x p
  rw [randomizedTailOn_insert _ hi, randomizedTailOn_insert _ hi,
    randomizedTailOn_congr (heq b), randomizedTailOn_congr (heq a),
    randomizedSlopeOn_congr (heq b), randomizedSlopeOn_congr (heq a)]
  simp only [Function.update_self]
  ring

/-- The two-coordinate polynomial expressed as arbitrary parameter updates. -/
theorem randomizedTailOn_update_update (p : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j) (a b w : ℝ) (k : ℕ) :
    randomizedTailOn (Function.update (Function.update p i a) j b)
      (insert i (insert j s)) w k = randomizedTailOn p s w k +
        (a + b) * randomizedSlopeOn p s w k + a * b * randomizedCoefficientOn p s w k := by
  have heq : ∀ l ∈ s, Function.update (Function.update p i a) j b l = p l := by
    intro l hl
    have hlj : l ≠ j := by
      intro h
      subst l
      exact hj hl
    have hli : l ≠ i := by
      intro h
      subst l
      exact hi hl
    rw [Function.update_of_ne hlj, Function.update_of_ne hli]
  rw [randomizedTailOn_insert_insert _ hi hj hij,
    randomizedTailOn_congr heq, randomizedSlopeOn_congr heq,
    randomizedCoefficientOn_congr heq]
  simp [Function.update_of_ne hij]

/-- Splitting two equal coordinates changes the randomized test by exactly
minus the mixed coefficient times the square of the displacement. -/
theorem randomizedTailOn_split (p : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j) (u t w : ℝ) (k : ℕ) :
    randomizedTailOn (Function.update (Function.update p i (u + t)) j (u - t))
        (insert i (insert j s)) w k -
      randomizedTailOn (Function.update (Function.update p i u) j u)
        (insert i (insert j s)) w k = -randomizedCoefficientOn p s w k * t ^ 2 := by
  rw [randomizedTailOn_update_update p hi hj hij,
    randomizedTailOn_update_update p hi hj hij]
  ring

variable {n : ℕ}

/-- The manuscript's randomized test `H`, on the full coordinate set. -/
def randomizedTail (p : Fin n → ℝ) (w : ℝ) (k : ℕ) : ℝ :=
  randomizedTailOn p univ w k

/-- The exact coefficient denoted `H_i` in the manuscript. -/
def randomizedGradient (p : Fin n → ℝ) (w : ℝ) (k : ℕ) (i : Fin n) : ℝ :=
  randomizedSlopeOn p (univ.erase i) w k

/-- The exact coefficient denoted `C_ij` in the manuscript, for distinct coordinates. -/
def randomizedMixedCoefficient (p : Fin n → ℝ) (w : ℝ) (k : ℕ)
    (i j : Fin n) : ℝ :=
  randomizedCoefficientOn p ((univ.erase i).erase j) w k

/-- The full-coordinate affine update identity characterizes `H_i` exactly. -/
theorem randomizedTail_update_sub (p : Fin n → ℝ) (i : Fin n) (a b w : ℝ) (k : ℕ) :
    randomizedTail (Function.update p i b) w k -
      randomizedTail (Function.update p i a) w k = (b - a) * randomizedGradient p w k i := by
  simpa [randomizedTail, randomizedGradient] using
    randomizedTailOn_update_sub p (notMem_erase i univ) a b w k

/-- The manuscript's identity `H_i - H_j = (p_j - p_i) C_ij`. -/
theorem randomizedGradient_sub (p : Fin n → ℝ) {i j : Fin n}
    (hij : i ≠ j) (w : ℝ) (k : ℕ) :
    randomizedGradient p w k i - randomizedGradient p w k j =
      (p j - p i) * randomizedMixedCoefficient p w k i j := by
  let s := (univ.erase i).erase j
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hsi : insert i s = univ.erase j := by
    ext x
    by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [s]
  have hsj : insert j s = univ.erase i := by
    ext x
    by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [s]
  simpa only [hsi, hsj, randomizedGradient, randomizedMixedCoefficient, s] using
    randomizedSlopeOn_insert_sub p hi hj w k

/-- Full-coordinate splitting identity for two equal original parameters. -/
theorem randomizedTail_split (p : Fin n → ℝ) {i j : Fin n}
    (hij : i ≠ j) (heq : p i = p j) (t w : ℝ) (k : ℕ) :
    randomizedTail (Function.update (Function.update p i (p i + t)) j (p j - t)) w k -
      randomizedTail p w k = -randomizedMixedCoefficient p w k i j * t ^ 2 := by
  let s := (univ.erase i).erase j
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hs : insert i (insert j s) = univ := by
    ext x
    by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [s]
  have hbase : Function.update (Function.update p i (p i)) j (p i) = p := by
    rw [Function.update_eq_self, heq, Function.update_eq_self]
  have hsplit := randomizedTailOn_split p hi hj hij (p i) t w k
  rw [hs, hbase] at hsplit
  simpa only [heq, randomizedTail, randomizedMixedCoefficient, s] using hsplit

end

end PoissonBinomialComparison
