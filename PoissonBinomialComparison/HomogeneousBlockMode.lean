import PoissonBinomialComparison.HomogeneousBlock
import PoissonBinomialComparison.LikelihoodRatio
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Modes of a homogeneous block with a fixed Bernoulli background

Interior parameters have fixed count support. Likelihood-ratio order of repeated
Bernoulli convolutions makes the derivative cross zero only from positive to
negative. Positive interior stationary points maximize the mass on `[0,1]`;
the maximum is strict for blocks of at least two coordinates.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Every valid homogeneous-block law has a positive mass somewhere. -/
theorem homogeneousBlockMass_exists_pos {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) : ∃ k, 0 < homogeneousBlockMass p s M t k := by
  induction M with
  | zero => exact pbMassIntOn_exists_pos s hp
  | succ M ih =>
    exact bernoulliConvolve_exists_pos (homogeneousBlockMass_nonneg hp M ht) ih ht.1 ht.2

private theorem homogeneousBlockMass_succ_pos_iff {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 < t ∧ t < 1) (k : ℤ) :
    0 < homogeneousBlockMass p s (M + 1) t k ↔
      0 < homogeneousBlockMass p s M t k ∨ 0 < homogeneousBlockMass p s M t (k - 1) := by
  have h0 := homogeneousBlockMass_nonneg hp M ⟨ht.1.le, ht.2.le⟩ k
  have h1 := homogeneousBlockMass_nonneg hp M ⟨ht.1.le, ht.2.le⟩ (k - 1)
  rw [homogeneousBlockMass_succ]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hz0 := le_antisymm hn.1 h0
    have hz1 := le_antisymm hn.2 h1
    simp [hz0, hz1] at h
  · rintro (h | h)
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht.2) h) (mul_nonneg ht.1.le h1)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2.le) h0) (mul_pos ht.1 h)

/-- On the open parameter interval, the count support is independent of the
homogeneous parameter, including deterministic background variables. -/
theorem homogeneousBlockMass_pos_iff {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (k : ℤ) :
    0 < homogeneousBlockMass p s M a k ↔ 0 < homogeneousBlockMass p s M b k := by
  induction M generalizing k with
  | zero => rfl
  | succ M ih =>
    rw [homogeneousBlockMass_succ_pos_iff hp M ha,
      homogeneousBlockMass_succ_pos_iff hp M hb, ih k, ih (k - 1)]

/-- Increasing the common block parameter increases the whole law in
likelihood-ratio order. -/
theorem homogeneousBlockMass_likelihoodRatio {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hab : a ≤ b) :
    LikelihoodRatioLE (homogeneousBlockMass p s M a) (homogeneousBlockMass p s M b) := by
  induction M with
  | zero => exact LikelihoodRatioLE.refl _
  | succ M ih =>
    exact (ih.convolve ha.1 ha.2).trans
      (bernoulliConvolve_likelihoodRatio (homogeneousBlockMass_cross hp M hb) hab)
      (homogeneousBlockMass_nonneg hp (M + 1) ha)
      (homogeneousBlockMass_nonneg hp (M + 1) hb)
      (bernoulliConvolve_exists_pos (homogeneousBlockMass_nonneg hp M hb)
        (homogeneousBlockMass_exists_pos hp M hb) ha.1 ha.2)

/-- A strict increase of a nonempty homogeneous block gives strict adjacent
likelihood-ratio comparison on positive overlapping support. -/
theorem homogeneousBlockMass_strict_adjacent {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hab : a < b) (k : ℤ)
    (ha0 : 0 < homogeneousBlockMass p s (M + 1) a k)
    (ha1 : 0 < homogeneousBlockMass p s (M + 1) a (k + 1))
    (hb1 : 0 < homogeneousBlockMass p s (M + 1) b (k + 1)) :
    homogeneousBlockMass p s (M + 1) b k * homogeneousBlockMass p s (M + 1) a (k + 1) <
      homogeneousBlockMass p s (M + 1) b (k + 1) * homogeneousBlockMass p s (M + 1) a k := by
  have hstep := bernoulliConvolve_strict_adjacent
    (homogeneousBlockMass_nonneg hp M ha) (homogeneousBlockMass_cross hp M ha)
    (homogeneousBlockMass_strictLogConcavity hp M ha) ha.1 ha.2 hab k ha0 ha1
  have hrest := (homogeneousBlockMass_likelihoodRatio hp M ha hb hab.le).convolve hb.1 hb.2
  exact hrest.strict_adjacent_trans (homogeneousBlockMass_nonneg hp (M + 1) ha)
    (bernoulliConvolve_nonneg (homogeneousBlockMass_nonneg hp M ha) hb.1 hb.2) k hstep hb1

/-- Adjacent differences cannot cross from nonpositive to positive as the
interior homogeneous parameter increases. -/
theorem homogeneousBlockMass_adjacent_sign_mono {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hab : a ≤ b) (k : ℤ)
    (hadj : homogeneousBlockMass p s M a (k - 1) ≤ homogeneousBlockMass p s M a k) :
    homogeneousBlockMass p s M b (k - 1) ≤ homogeneousBlockMass p s M b k := by
  by_cases hpos : 0 < homogeneousBlockMass p s M a k
  · have hlr := homogeneousBlockMass_likelihoodRatio hp M ⟨ha.1.le, ha.2.le⟩
      ⟨hb.1.le, hb.2.le⟩ hab (k - 1) k (by omega)
    have hmul := mul_le_mul_of_nonneg_left hadj
      (homogeneousBlockMass_nonneg hp M ⟨hb.1.le, hb.2.le⟩ k)
    exact (mul_le_mul_iff_left₀ hpos).mp (hlr.trans hmul)
  · have hzero : homogeneousBlockMass p s M a k = 0 :=
      le_antisymm (le_of_not_gt hpos) (homogeneousBlockMass_nonneg hp M ⟨ha.1.le, ha.2.le⟩ k)
    have hprev : ¬0 < homogeneousBlockMass p s M a (k - 1) := by rw [hzero] at hadj; exact not_lt.mpr hadj
    have hprevb : ¬0 < homogeneousBlockMass p s M b (k - 1) :=
      fun hh ↦ hprev ((homogeneousBlockMass_pos_iff hp M ha hb (k - 1)).mpr hh)
    exact (le_of_not_gt hprevb).trans (homogeneousBlockMass_nonneg hp M ⟨hb.1.le, hb.2.le⟩ k)

/-- The derivative can change sign only from positive to negative on `(0,1)`. -/
theorem homogeneousBlockMass_deriv_nonpos_mono {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hab : a ≤ b) (k : ℤ)
    (hd : deriv (fun t ↦ homogeneousBlockMass p s M t k) a ≤ 0) :
    deriv (fun t ↦ homogeneousBlockMass p s M t k) b ≤ 0 := by
  cases M with
  | zero => simp
  | succ M =>
    rw [deriv_homogeneousBlockMass_succ] at hd ⊢
    have hM : (0 : ℝ) < (M + 1 : ℕ) := by exact_mod_cast Nat.succ_pos M
    have hadj : homogeneousBlockMass p s M a (k - 1) ≤ homogeneousBlockMass p s M a k := by
      nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos hM.le
      (sub_nonpos.mpr (homogeneousBlockMass_adjacent_sign_mono hp M ha hb hab k hadj))

private theorem homogeneousBlockMass_deleted_tie {p : ι → ℝ} {s : Finset ι}
    (M : ℕ) (u : ℝ) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s (M + 1) u k)
    (hd : deriv (fun t ↦ homogeneousBlockMass p s (M + 1) t k) u = 0) :
    homogeneousBlockMass p s M u (k - 1) = homogeneousBlockMass p s M u k ∧
      0 < homogeneousBlockMass p s M u k := by
  rw [deriv_homogeneousBlockMass_succ] at hd
  have hM : (M + 1 : ℝ) ≠ 0 := by positivity
  have heq : homogeneousBlockMass p s M u (k - 1) = homogeneousBlockMass p s M u k := by
    have hz := (mul_eq_zero.mp hd).resolve_left (by exact_mod_cast hM)
    exact sub_eq_zero.mp hz
  refine ⟨heq, ?_⟩
  rw [homogeneousBlockMass_succ, heq] at hpos
  nlinarith

/-- For at least two varying coordinates, a positive stationary value forces
the derivative to be strictly negative at every larger interior parameter. -/
theorem homogeneousBlockMass_deriv_neg_after_critical {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {u t : ℝ}
    (hu : 0 < u ∧ u < 1) (ht : u < t ∧ t < 1) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s (M + 2) u k)
    (hd : deriv (fun v ↦ homogeneousBlockMass p s (M + 2) v k) u = 0) :
    deriv (fun v ↦ homogeneousBlockMass p s (M + 2) v k) t < 0 := by
  obtain ⟨heq, hupper⟩ := homogeneousBlockMass_deleted_tie (M + 1) u k hpos hd
  have ht' : 0 < t ∧ t < 1 := ⟨hu.1.trans ht.1, ht.2⟩
  have hnew := (homogeneousBlockMass_pos_iff hp (M + 1) hu ht' k).mp hupper
  have hstrict := homogeneousBlockMass_strict_adjacent hp M ⟨hu.1.le, hu.2.le⟩
    ⟨ht'.1.le, ht'.2.le⟩ ht.1 (k - 1) (by rw [heq]; exact hupper)
    (by simpa using hupper) (by simpa using hnew)
  simp only [sub_add_cancel, heq] at hstrict
  have hadj := (mul_lt_mul_iff_left₀ hupper).mp hstrict
  rw [show M + 2 = (M + 1) + 1 by omega, deriv_homogeneousBlockMass_succ]
  exact mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hadj)

/-- Before a positive stationary point of a block of size at least two, the
derivative is strictly positive throughout the interior parameter interval. -/
theorem homogeneousBlockMass_deriv_pos_before_critical {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {u t : ℝ}
    (hu : 0 < u ∧ u < 1) (ht : 0 < t ∧ t < u) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s (M + 2) u k)
    (hd : deriv (fun v ↦ homogeneousBlockMass p s (M + 2) v k) u = 0) :
    0 < deriv (fun v ↦ homogeneousBlockMass p s (M + 2) v k) t := by
  obtain ⟨heq, hupper⟩ := homogeneousBlockMass_deleted_tie (M + 1) u k hpos hd
  have ht' : 0 < t ∧ t < 1 := ⟨ht.1, ht.2.trans hu.2⟩
  have htupper := (homogeneousBlockMass_pos_iff hp (M + 1) hu ht' k).mp hupper
  have htlower := (homogeneousBlockMass_pos_iff hp (M + 1) hu ht' (k - 1)).mp
    (by rw [heq]; exact hupper)
  have hstrict := homogeneousBlockMass_strict_adjacent hp M ⟨ht'.1.le, ht'.2.le⟩
    ⟨hu.1.le, hu.2.le⟩ ht.2 (k - 1) htlower
    (by simpa using htupper) (by simpa using hupper)
  simp only [sub_add_cancel, heq] at hstrict
  have hadj := (mul_lt_mul_iff_right₀ hupper).mp hstrict
  rw [show M + 2 = (M + 1) + 1 by omega, deriv_homogeneousBlockMass_succ]
  exact mul_pos (by positivity) (sub_pos.mpr hadj)

/-- A stationary block of size one is constant as a function of its parameter. -/
theorem homogeneousBlockMass_one_eq_of_deriv_eq_zero (p : ι → ℝ) (s : Finset ι)
    (u t : ℝ) (k : ℤ)
    (hd : deriv (fun v ↦ homogeneousBlockMass p s 1 v k) u = 0) :
    homogeneousBlockMass p s 1 t k = homogeneousBlockMass p s 1 u k := by
  rw [deriv_homogeneousBlockMass_succ] at hd
  norm_num only [homogeneousBlockMass_zero, Nat.zero_add, Nat.cast_one, one_mul] at hd
  have heq := sub_eq_zero.mp hd
  simp only [homogeneousBlockMass_succ, homogeneousBlockMass_zero, heq]
  ring

/-- Every positive interior stationary point of a block of size at least two
is the unique global maximizer on the closed parameter interval `[0,1]`. -/
theorem homogeneousBlockMass_lt_of_critical {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {u t : ℝ}
    (hu : 0 < u ∧ u < 1) (ht : 0 ≤ t ∧ t ≤ 1) (htu : t ≠ u) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s (M + 2) u k)
    (hd : deriv (fun v ↦ homogeneousBlockMass p s (M + 2) v k) u = 0) :
    homogeneousBlockMass p s (M + 2) t k < homogeneousBlockMass p s (M + 2) u k := by
  have hdiff : Differentiable ℝ (fun v ↦ homogeneousBlockMass p s (M + 2) v k) :=
    fun v ↦ (hasDerivAt_homogeneousBlockMass p s (M + 2) v k).differentiableAt
  have hcont := hdiff.continuous
  rcases lt_or_gt_of_ne htu with htu | hut
  · have hmono : StrictMonoOn (fun v ↦ homogeneousBlockMass p s (M + 2) v k)
        (Set.Icc 0 u) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 u) hcont.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      exact homogeneousBlockMass_deriv_pos_before_critical hp M hu hx k hpos hd
    exact hmono ⟨ht.1, htu.le⟩ ⟨hu.1.le, le_rfl⟩ htu
  · have hanti : StrictAntiOn (fun v ↦ homogeneousBlockMass p s (M + 2) v k)
        (Set.Icc u 1) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc u 1) hcont.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      exact homogeneousBlockMass_deriv_neg_after_critical hp M hu hx k hpos hd
    exact hanti ⟨le_rfl, hu.2.le⟩ ⟨hut.le, ht.2⟩ hut

/-- Every positive interior stationary value is a global maximum, including
constant homogeneous blocks of size zero or one. -/
theorem homogeneousBlockMass_le_of_critical {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {u t : ℝ}
    (hu : 0 < u ∧ u < 1) (ht : 0 ≤ t ∧ t ≤ 1) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s M u k)
    (hd : deriv (fun v ↦ homogeneousBlockMass p s M v k) u = 0) :
    homogeneousBlockMass p s M t k ≤ homogeneousBlockMass p s M u k := by
  cases M with
  | zero => simp
  | succ M =>
    cases M with
    | zero => exact (homogeneousBlockMass_one_eq_of_deriv_eq_zero p s u t k hd).le
    | succ M =>
      by_cases htu : t = u
      · simp [htu]
      · exact (homogeneousBlockMass_lt_of_critical hp M hu ht htu k hpos hd).le

/-- Equal positive values at two interior parameters give a stationary point
strictly between them; positivity transfers along the fixed support. -/
theorem homogeneousBlockMass_exists_critical_between {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s M a k)
    (heq : homogeneousBlockMass p s M a k = homogeneousBlockMass p s M b k) :
    ∃ u, a < u ∧ u < b ∧ 0 < homogeneousBlockMass p s M u k ∧
      deriv (fun v ↦ homogeneousBlockMass p s M v k) u = 0 := by
  have hdiff : Differentiable ℝ (fun v ↦ homogeneousBlockMass p s M v k) :=
    fun v ↦ (hasDerivAt_homogeneousBlockMass p s M v k).differentiableAt
  obtain ⟨u, hu, hd⟩ := exists_deriv_eq_zero hab hdiff.continuous.continuousOn heq
  exact ⟨u, hu.1, hu.2, (homogeneousBlockMass_pos_iff hp M
    ⟨ha, hab.trans hb⟩ ⟨ha.trans hu.1, hu.2.trans hb⟩ k).mp hpos, hd⟩

/-- For a block of at least two coordinates, equal positive interior values
straddle exactly one stationary point, the strict global mode. -/
theorem homogeneousBlockMass_exists_unique_critical_of_eq {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s (M + 2) a k)
    (heq : homogeneousBlockMass p s (M + 2) a k = homogeneousBlockMass p s (M + 2) b k) :
    ∃! u, a < u ∧ u < b ∧ deriv (fun v ↦ homogeneousBlockMass p s (M + 2) v k) u = 0 := by
  obtain ⟨u, hau, hub, hupos, hdu⟩ :=
    homogeneousBlockMass_exists_critical_between hp (M + 2) ha hab hb k hpos heq
  refine ⟨u, ⟨hau, hub, hdu⟩, ?_⟩
  rintro y ⟨hay, hyb, hdy⟩
  have hu : 0 < u ∧ u < 1 := ⟨ha.trans hau, hub.trans hb⟩
  rcases lt_trichotomy y u with hyu | he | huy
  · have h := homogeneousBlockMass_deriv_pos_before_critical hp M hu
      ⟨ha.trans hay, hyu⟩ k hupos hdu
    rw [hdy] at h
    exact False.elim (lt_irrefl _ h)
  · exact he
  · have h := homogeneousBlockMass_deriv_neg_after_critical hp M hu
      ⟨huy, hyb.trans hb⟩ k hupos hdu
    rw [hdy] at h
    exact False.elim (lt_irrefl _ h)

end

end PoissonBinomialComparison
