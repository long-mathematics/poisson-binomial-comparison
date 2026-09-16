import PoissonBinomialComparison.Coordinate
import Mathlib.Tactic.Linarith

/-!
# Strict log-concavity of Bernoulli count masses

Integer indexing extends the existing subset-sum masses by zero at negative
counts. Cross-product inequalities are proved by induction under convolution
with a Bernoulli factor, without polynomial root machinery or Newton inequalities.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

/-- The cross-product form of log-concavity, including absence of internal zeros. -/
def MassCrossInequalities (f : ℤ → ℝ) : Prop :=
  ∀ i j : ℤ, i ≤ j → f (i - 1) * f (j + 1) ≤ f i * f j

/-- Strict log-concavity at every positive count mass, including support endpoints. -/
def StrictMassLogConcavity (f : ℤ → ℝ) : Prop :=
  ∀ k : ℤ, 0 < f k → f (k - 1) * f (k + 1) < (f k) ^ 2

/-- Cross-product inequalities control the mixed term in Bernoulli convolution. -/
theorem MassCrossInequalities.mixed {f : ℤ → ℝ} (h : MassCrossInequalities f)
    (i j : ℤ) (hij : i ≤ j) :
    f (i - 2) * f (j + 1) ≤ f i * f (j - 1) := by
  by_cases heq : i = j
  · subst j
    simpa [show i - 1 - 1 = i - 2 by omega, mul_comm] using
      h (i - 1) i (by omega)
  · have h1 := h (i - 1) j (by omega)
    have h2 := h i (j - 1) (by omega)
    simp only [show i - 1 - 1 = i - 2 by omega,
      show j - 1 + 1 = j by omega] at h1 h2
    exact h1.trans h2

/-- A nonnegative Bernoulli convolution preserves all mass cross inequalities. -/
theorem MassCrossInequalities.convolve {f : ℤ → ℝ} (h : MassCrossInequalities f)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    MassCrossInequalities (fun k ↦ v * f k + u * f (k - 1)) := by
  intro i j hij
  have h1 := mul_nonneg (sq_nonneg v) (sub_nonneg.mpr (h i j hij))
  have h2 := mul_nonneg (sq_nonneg u)
    (sub_nonneg.mpr (h (i - 1) (j - 1) (by omega)))
  have h3 := mul_nonneg (mul_nonneg hu hv) (sub_nonneg.mpr (h.mixed i j hij))
  simp only [show i - 1 - 1 = i - 2 by omega,
    show j - 1 + 1 = j by omega] at h2
  simp only [show i - 1 - 1 = i - 2 by omega,
    show j + 1 - 1 = j by omega]
  nlinarith

/-- A nonnegative Bernoulli convolution preserves strictness at positive masses. -/
theorem StrictMassLogConcavity.convolve {f : ℤ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hc : MassCrossInequalities f)
    (hs : StrictMassLogConcavity f) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    StrictMassLogConcavity (fun k ↦ v * f k + u * f (k - 1)) := by
  intro k hk
  have hc0 := hc k k le_rfl
  have hc1 := hc (k - 1) (k - 1) le_rfl
  have hmix := hc.mixed k k le_rfl
  simp only [show k - 1 - 1 = k - 2 by omega,
    show k - 1 + 1 = k by omega] at hc1
  have hvweak := mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hc0)
  have huweak := mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hc1)
  have hmixed := mul_nonneg (mul_nonneg hu hv) (sub_nonneg.mpr hmix)
  simp only [show k - 1 - 1 = k - 2 by omega,
    show k + 1 - 1 = k by omega]
  by_cases hpos : 0 < v * f k
  · have hvpos := pos_of_mul_pos_left hpos (hf k)
    have hfpos := pos_of_mul_pos_right hpos hv
    have hstrict := mul_pos (sq_pos_of_pos hvpos) (sub_pos.mpr (hs k hfpos))
    nlinarith
  · have hup : 0 < u * f (k - 1) := by linarith
    have hupos := pos_of_mul_pos_left hup (hf (k - 1))
    have hfpos := pos_of_mul_pos_right hup hu
    have hstrict := mul_pos (sq_pos_of_pos hupos) (sub_pos.mpr (hs (k - 1) hfpos))
    simp only [show k - 1 - 1 = k - 2 by omega,
      show k - 1 + 1 = k by omega] at hstrict
    nlinarith

/-- The cross-product inequalities rule out zeros between positive masses. -/
theorem MassCrossInequalities.positive_between {f : ℤ → ℝ}
    (h : MassCrossInequalities f) (hf : ∀ k, 0 ≤ f k)
    {i j k : ℤ} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : 0 < f i) (hk : 0 < f k) : 0 < f j := by
  by_cases hji : j = i
  · simpa [hji] using hi
  by_cases hjk' : j = k
  · simpa [hjk'] using hk
  have hcross : f i * f k ≤ f (i + 1) * f (k - 1) := by
    simpa using h (i + 1) (k - 1) (by omega)
  have hprod := (mul_pos hi hk).trans_le hcross
  have hi' := pos_of_mul_pos_left hprod (hf (k - 1))
  exact MassCrossInequalities.positive_between h hf (i := i + 1) (by omega) hjk hi' hk
termination_by (j - i).toNat
decreasing_by omega

variable {ι : Type*} [DecidableEq ι]

/-- Existing subset-sum count masses, extended by zero to negative integer counts. -/
def pbMassIntOn (p : ι → ℝ) (s : Finset ι) (k : ℤ) : ℝ :=
  if 0 ≤ k then pbMassOn p s k.toNat else 0

/-- Integer indexing agrees exactly with the original mass at natural counts. -/
@[simp] theorem pbMassIntOn_natCast (p : ι → ℝ) (s : Finset ι) (k : ℕ) :
    pbMassIntOn p s k = pbMassOn p s k := by
  simp [pbMassIntOn]

theorem pbMassIntOn_of_neg (p : ι → ℝ) (s : Finset ι) {k : ℤ} (hk : k < 0) :
    pbMassIntOn p s k = 0 := by
  simp [pbMassIntOn, not_le.mpr hk]

theorem pbMassIntOn_nonneg {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (k : ℤ) :
    0 ≤ pbMassIntOn p s k := by
  unfold pbMassIntOn
  split
  · exact pbMassOn_nonneg hp _
  · exact le_rfl

/-- The deletion recurrence with integer indexing handles zero counts uniformly. -/
theorem pbMassIntOn_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (k : ℤ) :
    pbMassIntOn p (insert i s) k =
      (1 - p i) * pbMassIntOn p s k + p i * pbMassIntOn p s (k - 1) := by
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    cases k with
    | zero => simp [pbMassIntOn, pbMassOn_insert_zero p hi]
    | succ k =>
      have hcast : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
      simp only [hcast, pbMassIntOn_natCast]
      exact pbMassOn_insert_succ p hi k
  · have hk' : ¬0 ≤ k - 1 := by omega
    simp only [pbMassIntOn, hk, hk', ite_false, mul_zero, add_zero]

@[simp] theorem pbMassIntOn_empty (p : ι → ℝ) (k : ℤ) :
    pbMassIntOn p ∅ k = if k = 0 then 1 else 0 := by
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    by_cases hk0 : k = 0
    · subst k
      simp [pbMassIntOn]
    · simp [pbMassOn_eq_sum_powerset, bernoulliWeight, hk0, Ne.symm hk0]
  · have hk' : k ≠ 0 := by omega
    simp [pbMassIntOn, hk, hk']

/-- All Bernoulli masses satisfy the separated-index cross-product inequalities. -/
theorem pbMassIntOn_cross {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) :
    MassCrossInequalities (pbMassIntOn p s) := by
  induction s using Finset.induction_on with
  | empty =>
    intro i j hij
    by_cases hi : i - 1 = 0
    · have hj : j + 1 ≠ 0 := by omega
      simp only [pbMassIntOn_empty, hi, hj, ite_false, ite_true, mul_zero]
      positivity
    · simp only [pbMassIntOn_empty, hi, ite_false, zero_mul]
      positivity
  | @insert i s hi ih =>
    have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 :=
      fun j hj ↦ hp j (mem_insert_of_mem hj)
    have hpi := hp i (mem_insert_self i s)
    have heq : pbMassIntOn p (insert i s) =
        (fun k ↦ (1 - p i) * pbMassIntOn p s k + p i * pbMassIntOn p s (k - 1)) :=
      funext (pbMassIntOn_insert p hi)
    rw [heq]
    exact (ih hps).convolve hpi.1 (sub_nonneg.mpr hpi.2)

/-- Bernoulli count masses are strictly log-concave at every positive mass. -/
theorem pbMassIntOn_strictLogConcavity {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) :
    StrictMassLogConcavity (pbMassIntOn p s) := by
  induction s using Finset.induction_on with
  | empty =>
    intro k hk
    have hk0 : k = 0 := by
      by_contra h
      simp [h] at hk
    subst k
    norm_num
  | @insert i s hi ih =>
    have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 :=
      fun j hj ↦ hp j (mem_insert_of_mem hj)
    have hpi := hp i (mem_insert_self i s)
    have heq : pbMassIntOn p (insert i s) =
        (fun k ↦ (1 - p i) * pbMassIntOn p s k + p i * pbMassIntOn p s (k - 1)) :=
      funext (pbMassIntOn_insert p hi)
    rw [heq]
    exact (ih hps).convolve (pbMassIntOn_nonneg hps) (pbMassIntOn_cross s hps)
      hpi.1 (sub_nonneg.mpr hpi.2)

/-- Bernoulli count masses have interval support, with deterministic cases included. -/
theorem pbMassIntOn_positive_between {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    {i j k : ℤ} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : 0 < pbMassIntOn p s i) (hk : 0 < pbMassIntOn p s k) :
    0 < pbMassIntOn p s j :=
  (pbMassIntOn_cross s hp).positive_between (pbMassIntOn_nonneg hp) hij hjk hi hk

/-- Log-concavity stated entirely in the original natural-index mass representation. -/
theorem pbMassOn_logConcave {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (k : ℕ) :
    pbMassOn p s k * pbMassOn p s (k + 2) ≤ (pbMassOn p s (k + 1)) ^ 2 := by
  have h := pbMassIntOn_cross s hp ((k + 1 : ℕ) : ℤ) ((k + 1 : ℕ) : ℤ) le_rfl
  have h0 : ((k + 1 : ℕ) : ℤ) - 1 = k := by omega
  have h2 : ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) := by omega
  simpa only [h0, h2, pbMassIntOn_natCast, pow_two] using h

/-- Strict log-concavity holds whenever the middle count mass is positive. -/
theorem pbMassOn_strictLogConcave {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (k : ℕ)
    (hk : 0 < pbMassOn p s (k + 1)) :
    pbMassOn p s k * pbMassOn p s (k + 2) < (pbMassOn p s (k + 1)) ^ 2 := by
  have hpos : 0 < pbMassIntOn p s ((k + 1 : ℕ) : ℤ) := by
    rw [pbMassIntOn_natCast]
    exact hk
  have h := pbMassIntOn_strictLogConcavity s hp ((k + 1 : ℕ) : ℤ) hpos
  have h0 : ((k + 1 : ℕ) : ℤ) - 1 = k := by omega
  have h2 : ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) := by omega
  simpa only [h0, h2, pbMassIntOn_natCast] using h

/-- Interval support in the original natural-index mass representation. -/
theorem pbMassOn_positive_between {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : 0 < pbMassOn p s i) (hk : 0 < pbMassOn p s k) :
    0 < pbMassOn p s j := by
  have h := pbMassIntOn_positive_between s hp
    (i := (i : ℤ)) (j := (j : ℤ)) (k := (k : ℤ))
    (by exact_mod_cast hij) (by exact_mod_cast hjk) (by simpa using hi) (by simpa using hk)
  simpa using h

variable {n : ℕ}

/-- Manuscript log-concavity of the count mass function. -/
theorem pbMass_logConcave {p : Fin n → ℝ} (hp : ValidParameters p) (k : ℕ) :
    pbMass p k * pbMass p (k + 2) ≤ (pbMass p (k + 1)) ^ 2 :=
  pbMassOn_logConcave univ (fun i _ ↦ hp i) k

/-- Manuscript strict log-concavity, under the weaker assumption of a positive middle mass. -/
theorem pbMass_strictLogConcave {p : Fin n → ℝ} (hp : ValidParameters p) (k : ℕ)
    (hk : 0 < pbMass p (k + 1)) :
    pbMass p k * pbMass p (k + 2) < (pbMass p (k + 1)) ^ 2 :=
  pbMassOn_strictLogConcave univ (fun i _ ↦ hp i) k hk

/-- Manuscript interval support of the count mass function. -/
theorem pbMass_positive_between {p : Fin n → ℝ} (hp : ValidParameters p)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : 0 < pbMass p i) (hk : 0 < pbMass p k) : 0 < pbMass p j :=
  pbMassOn_positive_between univ (fun i _ ↦ hp i) hij hjk hi hk

end

end PoissonBinomialComparison
