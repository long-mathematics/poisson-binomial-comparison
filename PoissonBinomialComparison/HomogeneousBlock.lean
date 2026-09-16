import PoissonBinomialComparison.Adjoining
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# A homogeneous Bernoulli block with a fixed background law

`homogeneousBlockMass p s M t k` is the mass at integer count `k` after
adjoining `M` Bernoulli parameters equal to `t` to the fixed law on `s`.
The recursive finite convolution is proved equivalent to the subset-sum law
whenever the homogeneous block is represented by a disjoint coordinate set.
Differentiating the recursion proves the manuscript's exact `g_M` derivative;
the adjoining criterion is then a theorem about that analytic derivative.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- The manuscript's `g_M(t) = P(Bin(M,t) + W = k)`, with `W` the count on `s`.
Integer count indexing uses the existing zero-extended subset-sum masses. -/
def homogeneousBlockMass (p : ι → ℝ) (s : Finset ι) : ℕ → ℝ → ℤ → ℝ
  | 0, _, k => pbMassIntOn p s k
  | M + 1, t, k => (1 - t) * homogeneousBlockMass p s M t k +
      t * homogeneousBlockMass p s M t (k - 1)

@[simp] theorem homogeneousBlockMass_zero (p : ι → ℝ) (s : Finset ι) (t : ℝ) (k : ℤ) :
    homogeneousBlockMass p s 0 t k = pbMassIntOn p s k := rfl

/-- The defining Bernoulli convolution recurrence. -/
theorem homogeneousBlockMass_succ (p : ι → ℝ) (s : Finset ι)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    homogeneousBlockMass p s (M + 1) t k =
      (1 - t) * homogeneousBlockMass p s M t k +
        t * homogeneousBlockMass p s M t (k - 1) := rfl

/-- The iterated convolution equals the original subset law for any disjoint
coordinate block on which all parameters equal `t`. -/
theorem homogeneousBlockMass_eq_union (p : ι → ℝ) (s u : Finset ι)
    (hdisj : Disjoint s u) (t : ℝ) (hconst : ∀ i ∈ u, p i = t) (k : ℤ) :
    homogeneousBlockMass p s u.card t k = pbMassIntOn p (s ∪ u) k := by
  induction u using Finset.induction_on generalizing k with
  | empty => simp
  | @insert i u hi ih =>
    have hdi : i ∉ s := by
      intro his
      exact disjoint_left.mp hdisj his (mem_insert_self i u)
    have hdu : Disjoint s u := hdisj.mono_right (subset_insert i u)
    have hcu : ∀ j ∈ u, p j = t := fun j hj ↦ hconst j (mem_insert_of_mem hj)
    have hpi := hconst i (mem_insert_self i u)
    rw [card_insert_of_notMem hi, homogeneousBlockMass_succ,
      ih hdu hcu k, ih hdu hcu (k - 1), union_insert,
      pbMassIntOn_insert p (by simp [hdi, hi]), hpi]

/-- Moving a fixed-background addition past the homogeneous block commutes
Bernoulli convolutions. -/
theorem homogeneousBlockMass_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (M : ℕ) (t : ℝ) (k : ℤ) :
    homogeneousBlockMass p (insert i s) M t k =
      (1 - p i) * homogeneousBlockMass p s M t k +
        p i * homogeneousBlockMass p s M t (k - 1) := by
  induction M generalizing k with
  | zero => exact pbMassIntOn_insert p hi k
  | succ M ih =>
    simp only [homogeneousBlockMass_succ, ih]
    ring

/-- Nonnegativity of the homogeneous-block law for valid parameters. -/
theorem homogeneousBlockMass_nonneg {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (k : ℤ) : 0 ≤ homogeneousBlockMass p s M t k := by
  induction M generalizing k with
  | zero => exact pbMassIntOn_nonneg hp k
  | succ M ih =>
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (ih k))
      (mul_nonneg ht.1 (ih (k - 1)))

/-- Cross-product inequalities pass to a homogeneous block by convolution. -/
theorem homogeneousBlockMass_cross {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) : MassCrossInequalities (homogeneousBlockMass p s M t) := by
  induction M with
  | zero => exact pbMassIntOn_cross s hp
  | succ M ih => exact ih.convolve ht.1 (sub_nonneg.mpr ht.2)

/-- Strict log-concavity, including deterministic support endpoints, passes to the block. -/
theorem homogeneousBlockMass_strictLogConcavity {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) : StrictMassLogConcavity (homogeneousBlockMass p s M t) := by
  induction M with
  | zero => exact pbMassIntOn_strictLogConcavity s hp
  | succ M ih =>
    exact ih.convolve (homogeneousBlockMass_nonneg hp M ht)
      (homogeneousBlockMass_cross hp M ht) ht.1 (sub_nonneg.mpr ht.2)

/-- The exact derivative for a nonempty homogeneous block, proved from its
finite convolution polynomial. -/
theorem hasDerivAt_homogeneousBlockMass_succ (p : ι → ℝ) (s : Finset ι)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    HasDerivAt (fun u ↦ homogeneousBlockMass p s (M + 1) u k)
      ((M + 1 : ℕ) * (homogeneousBlockMass p s M t (k - 1) -
        homogeneousBlockMass p s M t k)) t := by
  induction M generalizing k with
  | zero =>
    have hd := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul
      (hasDerivAt_const t (pbMassIntOn p s k))).add
      ((hasDerivAt_id t).mul (hasDerivAt_const t (pbMassIntOn p s (k - 1))))
    convert hd using 1
    · rfl
    · simp only [homogeneousBlockMass_zero, zero_sub,
        Pi.sub_apply, id_eq, mul_zero, add_zero, one_mul]
      ring
  | succ M ih =>
    have hd := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul (ih k)).add
      ((hasDerivAt_id t).mul (ih (k - 1)))
    convert hd using 1
    · rfl
    · simp only [homogeneousBlockMass_succ, Nat.cast_add, Nat.cast_one, Pi.sub_apply, id_eq]
      ring

/-- The derivative formula in the manuscript's dimension notation, also valid
for the constant block of size zero because its prefactor is zero. -/
theorem hasDerivAt_homogeneousBlockMass (p : ι → ℝ) (s : Finset ι)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    HasDerivAt (fun u ↦ homogeneousBlockMass p s M u k)
      ((M : ℝ) * (homogeneousBlockMass p s (M - 1) t (k - 1) -
        homogeneousBlockMass p s (M - 1) t k)) t := by
  cases M with
  | zero => simpa using hasDerivAt_const t (pbMassIntOn p s k)
  | succ M => simpa using hasDerivAt_homogeneousBlockMass_succ p s M t k

/-- Derivative rewriting interface for the manuscript's `g_M` formula. -/
theorem deriv_homogeneousBlockMass_succ (p : ι → ℝ) (s : Finset ι)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    deriv (fun u ↦ homogeneousBlockMass p s (M + 1) u k) t =
      (M + 1 : ℕ) * (homogeneousBlockMass p s M t (k - 1) -
        homogeneousBlockMass p s M t k) :=
  (hasDerivAt_homogeneousBlockMass_succ p s M t k).deriv

/-- The manuscript's derivative identity as an equality of real numbers. -/
theorem deriv_homogeneousBlockMass (p : ι → ℝ) (s : Finset ι)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    deriv (fun u ↦ homogeneousBlockMass p s M u k) t =
      (M : ℝ) * (homogeneousBlockMass p s (M - 1) t (k - 1) -
        homogeneousBlockMass p s (M - 1) t k) :=
  (hasDerivAt_homogeneousBlockMass p s M t k).deriv

/-- The positive-height, nonpositive-derivative criterion gives adjacent mass
order in the full homogeneous-block law, as in the manuscript's corollary. -/
theorem homogeneousBlockMass_adjacent_le_of_deriv_nonpos {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (k : ℤ)
    (hk : 0 < homogeneousBlockMass p s (M + 1) t k)
    (hd : deriv (fun u ↦ homogeneousBlockMass p s (M + 1) u k) t ≤ 0) :
    homogeneousBlockMass p s (M + 1) t (k - 1) ≤
      homogeneousBlockMass p s (M + 1) t k := by
  rw [deriv_homogeneousBlockMass_succ] at hd
  have hM : (0 : ℝ) < (M + 1 : ℕ) := by exact_mod_cast Nat.succ_pos M
  have hadj : homogeneousBlockMass p s M t (k - 1) ≤ homogeneousBlockMass p s M t k := by
    have hdiff : homogeneousBlockMass p s M t (k - 1) -
        homogeneousBlockMass p s M t k ≤ 0 := by nlinarith
    linarith
  have hbase : 0 < homogeneousBlockMass p s M t k := by
    rw [homogeneousBlockMass_succ] at hk
    have hmul := mul_le_mul_of_nonneg_left hadj ht.1
    linarith
  have hprefix := (homogeneousBlockMass_cross hp M ht).prefix_order
    (homogeneousBlockMass_nonneg hp M ht) hbase hadj
  rw [homogeneousBlockMass_succ, homogeneousBlockMass_succ]
  exact add_le_add (mul_le_mul_of_nonneg_left hadj (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left (hprefix (k - 1) (by omega)) ht.1)

private theorem homogeneousBlockMass_union_prefix_order {p : ι → ℝ} (s u : Finset ι)
    (hp : ∀ i ∈ s ∪ u, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) (t : ℝ) (k : ℤ)
    (hprefix : ∀ j ≤ k, homogeneousBlockMass p s M t (j - 1) ≤
      homogeneousBlockMass p s M t j) :
    homogeneousBlockMass p (s ∪ u) M t k ≤ homogeneousBlockMass p s M t k ∧
      ∀ j ≤ k, homogeneousBlockMass p (s ∪ u) M t (j - 1) ≤
        homogeneousBlockMass p (s ∪ u) M t j := by
  induction u using Finset.induction_on with
  | empty => simpa using And.intro (le_refl (homogeneousBlockMass p s M t k)) hprefix
  | @insert i u hi ih =>
    have hps : ∀ j ∈ s ∪ u, 0 ≤ p j ∧ p j ≤ 1 := by
      intro j hj
      exact hp j (by simp only [mem_union, mem_insert] at hj ⊢; tauto)
    obtain ⟨hle, hpre⟩ := ih hps
    have hpi := hp i (by simp)
    rw [union_insert]
    by_cases him : i ∈ s ∪ u
    · rw [insert_eq_of_mem him]
      exact ⟨hle, hpre⟩
    · constructor
      · rw [homogeneousBlockMass_insert p him]
        have hmul := mul_le_mul_of_nonneg_left (hpre k le_rfl) hpi.1
        linarith
      · intro j hj
        rw [homogeneousBlockMass_insert p him, homogeneousBlockMass_insert p him]
        exact add_le_add (mul_le_mul_of_nonneg_left (hpre j hj) (sub_nonneg.mpr hpi.2))
          (mul_le_mul_of_nonneg_left (hpre (j - 1) (by omega)) hpi.1)

/-- The full derivative criterion for adjoining: after a positive homogeneous-block
mass has nonpositive derivative, any finite collection of further valid independent
Bernoulli parameters can only decrease that mass. -/
theorem homogeneousBlockMass_union_le_of_deriv_nonpos {p : ι → ℝ} (s u : Finset ι)
    (hp : ∀ i ∈ s ∪ u, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (k : ℤ)
    (hk : 0 < homogeneousBlockMass p s (M + 1) t k)
    (hd : deriv (fun v ↦ homogeneousBlockMass p s (M + 1) v k) t ≤ 0) :
    homogeneousBlockMass p (s ∪ u) (M + 1) t k ≤
      homogeneousBlockMass p s (M + 1) t k := by
  have hps : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1 := fun i hi ↦ hp i (mem_union_left u hi)
  have hadj := homogeneousBlockMass_adjacent_le_of_deriv_nonpos hps M ht k hk hd
  have hprefix := (homogeneousBlockMass_cross hps (M + 1) ht).prefix_order
    (homogeneousBlockMass_nonneg hps (M + 1) ht) hk hadj
  exact (homogeneousBlockMass_union_prefix_order s u hp (M + 1) t k hprefix).1

end

end PoissonBinomialComparison
