import PoissonBinomialComparison.HomogeneousBlockMode

/-!
# Excluding the remaining nonhomogeneous lower blocks

The fixed background may be any valid finite Bernoulli law; in particular it
includes `W = Bin(s+1, λ)` with `λ` at either endpoint. The single-positive-value
case adjoins the missing variables at the old parameter first, then raises the
whole block. This is an equivalent finite-law proof of the manuscript's strict
comparison and avoids imposing any nondegeneracy assumption on the background.
-/

namespace PoissonBinomialComparison

open scoped Topology
open Finset Set

noncomputable section

variable {ι : Type*} [DecidableEq ι] {p : ι → ℝ} {s : Finset ι}

/-- Adding homogeneous Bernoulli variables preserves prefix mass order and
cannot increase the target mass. -/
theorem homogeneousBlockMass_add_prefix (M b : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (k : ℤ)
    (hprefix : ∀ j ≤ k, homogeneousBlockMass p s M t (j - 1) ≤ homogeneousBlockMass p s M t j) :
    homogeneousBlockMass p s (M + b) t k ≤ homogeneousBlockMass p s M t k ∧
      ∀ j ≤ k, homogeneousBlockMass p s (M + b) t (j - 1) ≤
        homogeneousBlockMass p s (M + b) t j := by
  induction b with
  | zero => simpa using And.intro (le_refl (homogeneousBlockMass p s M t k)) hprefix
  | succ b ih =>
    have hadj := ih.2 k le_rfl
    constructor
    · rw [show M + (b + 1) = (M + b) + 1 by omega, homogeneousBlockMass_succ]
      have hstep : (1 - t) * homogeneousBlockMass p s (M + b) t k +
          t * homogeneousBlockMass p s (M + b) t (k - 1) ≤ homogeneousBlockMass p s (M + b) t k := by
        nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hadj)]
      exact hstep.trans ih.1
    · intro j hj
      rw [show M + (b + 1) = (M + b) + 1 by omega,
        homogeneousBlockMass_succ, homogeneousBlockMass_succ]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (ih.2 j hj) (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (ih.2 (j - 1) (by omega)) ht.1)

/-- Interior homogeneous additions retain every positive target mass. -/
theorem homogeneousBlockMass_add_pos (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (M b : ℕ) {t : ℝ} (ht : 0 < t ∧ t < 1) (k : ℤ)
    (hk : 0 < homogeneousBlockMass p s M t k) :
    0 < homogeneousBlockMass p s (M + b) t k := by
  induction b with
  | zero => simpa using hk
  | succ b ih =>
    rw [show M + (b + 1) = (M + b) + 1 by omega, homogeneousBlockMass_succ]
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht.2) ih)
      (mul_nonneg ht.1.le (homogeneousBlockMass_nonneg hp _ ⟨ht.1.le, ht.2.le⟩ _))

/-- A positive interior mass of a block of size at least two strictly decreases
after any point where its derivative is nonpositive. -/
theorem homogeneousBlockMass_lt_after_nonpos (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (M : ℕ) {v a : ℝ} (hv : 0 < v) (hva : v < a) (ha : a < 1) (k : ℤ)
    (hk : 0 < homogeneousBlockMass p s (M + 2) v k)
    (hd : deriv (fun t ↦ homogeneousBlockMass p s (M + 2) t k) v ≤ 0) :
    homogeneousBlockMass p s (M + 2) a k < homogeneousBlockMass p s (M + 2) v k := by
  have hdiff : Differentiable ℝ (fun t ↦ homogeneousBlockMass p s (M + 2) t k) :=
    fun t ↦ (hasDerivAt_homogeneousBlockMass p s _ t k).differentiableAt
  have hanti : AntitoneOn (fun t ↦ homogeneousBlockMass p s (M + 2) t k) (Icc v a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v a) hdiff.continuous.continuousOn hdiff.differentiableOn
    intro t ht
    rw [interior_Icc] at ht
    exact homogeneousBlockMass_deriv_nonpos_mono hp _ ⟨hv, hva.trans ha⟩
      ⟨hv.trans ht.1, ht.2.trans ha⟩ ht.1.le k hd
  have hle := hanti ⟨le_rfl, hva.le⟩ ⟨hva.le, le_rfl⟩ hva.le
  apply lt_of_le_of_ne hle
  intro heq
  obtain ⟨u, hvu, hua, hupos, hdu⟩ := homogeneousBlockMass_exists_critical_between hp _ hv hva ha k hk heq.symm
  have hlt := homogeneousBlockMass_lt_of_critical hp M ⟨hv.trans hvu, hua.trans ha⟩
    ⟨hv.le, (hva.trans ha).le⟩ hvu.ne k hupos hdu
  exact not_lt_of_ge (hanti ⟨le_rfl, hva.le⟩ ⟨hvu.le, hua.le⟩ hvu.le) hlt

/-- A positive tied adjacent pair becomes strictly ordered after one positive addition. -/
theorem homogeneousBlockMass_succ_adjacent_lt_of_tie
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 < t ∧ t ≤ 1) (k : ℤ) (hk : 0 < homogeneousBlockMass p s M t k)
    (heq : homogeneousBlockMass p s M t (k - 1) = homogeneousBlockMass p s M t k) :
    homogeneousBlockMass p s (M + 1) t (k - 1) < homogeneousBlockMass p s (M + 1) t k := by
  have hlc := homogeneousBlockMass_strictLogConcavity hp M ⟨ht.1.le, ht.2⟩ (k - 1)
    (by rw [heq]; exact hk)
  simp only [sub_add_cancel, heq, pow_two] at hlc
  have hprev := (mul_lt_mul_iff_left₀ hk).mp hlc
  simp only [homogeneousBlockMass_succ, heq]
  nlinarith [mul_pos ht.1 (sub_pos.mpr hprev)]

/-- QONE: one smaller positive coordinate and a stationary block of `M`
larger coordinates cannot match the upper homogeneous free gradient. -/
theorem lower_two_values_block_lt (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    {M b : ℕ} (hM : 1 ≤ M) (hr : 3 ≤ M + b + 1) {v a : ℝ}
    (hv : 0 < v) (hva : v < a) (ha : a < 1) (k : ℤ)
    (hk : 0 < homogeneousBlockMass p s M v k)
    (hd : deriv (fun t ↦ homogeneousBlockMass p s M t k) v = 0) :
    homogeneousBlockMass p s (M + b) a k < homogeneousBlockMass p s M v k := by
  have hv' : 0 < v ∧ v < 1 := ⟨hv, hva.trans ha⟩
  have ha' : 0 < a ∧ a < 1 := ⟨hv.trans hva, ha⟩
  have ha0 : 0 ≤ a ∧ a ≤ 1 := ⟨ha'.1.le, ha.le⟩
  by_cases hM1 : M = 1
  · subst M
    have hb : 1 ≤ b := by omega
    have hconst := homogeneousBlockMass_one_eq_of_deriv_eq_zero p s v a k hd
    have hk1 : 0 < homogeneousBlockMass p s 1 a k := by rwa [hconst]
    have htie : pbMassIntOn p s (k - 1) = pbMassIntOn p s k := by
      simpa only [deriv_homogeneousBlockMass_succ, homogeneousBlockMass_zero,
        Nat.zero_add, Nat.cast_one, one_mul, sub_eq_zero] using hd
    have hk0 : 0 < homogeneousBlockMass p s 0 a k := by
      simpa only [homogeneousBlockMass_succ, homogeneousBlockMass_zero, htie,
        show (1 - a) * pbMassIntOn p s k + a * pbMassIntOn p s k = pbMassIntOn p s k by ring] using hk1
    have hadj := homogeneousBlockMass_succ_adjacent_lt_of_tie hp 0 ⟨ha'.1, ha.le⟩ k hk0 htie
    have hprefix := (homogeneousBlockMass_cross hp 1 ha0).prefix_order
      (homogeneousBlockMass_nonneg hp 1 ha0) hk1 hadj.le
    have hlt : homogeneousBlockMass p s 2 a k < homogeneousBlockMass p s 1 a k := by
      rw [show 2 = 1 + 1 by rfl, homogeneousBlockMass_succ]
      nlinarith [mul_pos ha'.1 (sub_pos.mpr hadj)]
    have hprefix2 := (homogeneousBlockMass_add_prefix 1 1 ha0 k hprefix).2
    have hle := (homogeneousBlockMass_add_prefix 2 (b - 1) ha0 k hprefix2).1
    rw [show 2 + (b - 1) = 1 + b by omega] at hle
    exact (hle.trans_lt hlt).trans_eq hconst
  · obtain ⟨L, rfl⟩ : ∃ L, M = L + 2 := ⟨M - 2, by omega⟩
    have hlt := homogeneousBlockMass_lt_of_critical hp L hv' ha0 hva.ne' k hk hd
    have hpos := (homogeneousBlockMass_pos_iff hp (L + 2) hv' ha' k).mp hk
    have hder := homogeneousBlockMass_deriv_neg_after_critical hp L hv' ⟨hva, ha⟩ k hk hd
    have hadj := homogeneousBlockMass_adjacent_le_of_deriv_nonpos hp (L + 1) ha0 k hpos hder.le
    have hprefix := (homogeneousBlockMass_cross hp (L + 2) ha0).prefix_order
      (homogeneousBlockMass_nonneg hp (L + 2) ha0) hpos hadj
    exact (homogeneousBlockMass_add_prefix (L + 2) b ha0 k hprefix).1.trans_lt hlt

/-- QZERO: a positive homogeneous lower block with at least one zero coordinate
cannot match the upper homogeneous free gradient when the zero-coordinate KKT
inequality holds. -/
theorem lower_positive_and_zero_block_lt (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    {M b : ℕ} (hM : 1 ≤ M) (hb : 1 ≤ b) (hr : 3 ≤ M + b) {v a : ℝ}
    (hv : 0 < v) (hva : v < a) (ha : a < 1) (k : ℤ)
    (hk : 0 < homogeneousBlockMass p s (M - 1) v k)
    (hzero : homogeneousBlockMass p s M v k ≤ homogeneousBlockMass p s (M - 1) v k) :
    homogeneousBlockMass p s (M + b - 1) a k < homogeneousBlockMass p s (M - 1) v k := by
  have hv' : 0 < v ∧ v < 1 := ⟨hv, hva.trans ha⟩
  have hv0 : 0 ≤ v ∧ v ≤ 1 := ⟨hv.le, (hva.trans ha).le⟩
  have hadj : homogeneousBlockMass p s (M - 1) v (k - 1) ≤ homogeneousBlockMass p s (M - 1) v k := by
    rw [show M = (M - 1) + 1 by omega, homogeneousBlockMass_succ] at hzero
    simp only [Nat.add_sub_cancel] at hzero
    nlinarith
  have hprefix := (homogeneousBlockMass_cross hp (M - 1) hv0).prefix_order
    (homogeneousBlockMass_nonneg hp (M - 1) hv0) hk hadj
  have hle := (homogeneousBlockMass_add_prefix (M - 1) b hv0 k hprefix).1
  have hpos := homogeneousBlockMass_add_pos hp (M - 1) b hv' k hk
  rw [show M - 1 + b = M + b - 1 by omega] at hle hpos
  have hdeleted := (homogeneousBlockMass_add_prefix (M - 1) (b - 1) hv0 k hprefix).2 k le_rfl
  have hd : deriv (fun t ↦ homogeneousBlockMass p s (M + b - 1) t k) v ≤ 0 := by
    rw [deriv_homogeneousBlockMass]
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    apply sub_nonpos.mpr
    convert hdeleted using 1 <;> congr 2 <;> omega
  have hlt := homogeneousBlockMass_lt_after_nonpos hp (M + b - 3) hv hva ha k
    (by simpa only [show M + b - 3 + 2 = M + b - 1 by omega] using hpos)
    (by simpa only [show M + b - 3 + 2 = M + b - 1 by omega] using hd)
  rw [show M + b - 3 + 2 = M + b - 1 by omega] at hlt
  exact hlt.trans_le hle

/-- The exact free-gradient contradiction for QONE. The smaller positive
coordinate has been deleted, leaving `M` copies of the larger value and `b`
zeros, so the upper free gradient is the block of size `M+b`. -/
theorem not_lower_two_values_stationary
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {M b : ℕ}
    (hM : 1 ≤ M) (hr : 3 ≤ M + b + 1) {v a c : ℝ}
    (hv : 0 < v) (hva : v < a) (ha : a < 1) (hc : 0 < c) (k : ℤ)
    (hvgrad : homogeneousBlockMass p s M v k = c)
    (hagrad : homogeneousBlockMass p s (M + b) a k = c)
    (hd : deriv (fun t ↦ homogeneousBlockMass p s M t k) v = 0) : False := by
  have hlt := lower_two_values_block_lt hp hM hr hv hva ha k (by rwa [hvgrad]) hd
  rw [hvgrad, hagrad] at hlt
  exact lt_irrefl _ hlt

/-- The exact free-gradient and zero-coordinate KKT contradiction for QZERO. -/
theorem not_lower_positive_and_zero_stationary
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {M b : ℕ}
    (hM : 1 ≤ M) (hb : 1 ≤ b) (hr : 3 ≤ M + b) {v a c : ℝ}
    (hv : 0 < v) (hva : v < a) (ha : a < 1) (hc : 0 < c) (k : ℤ)
    (hvgrad : homogeneousBlockMass p s (M - 1) v k = c)
    (hzero : homogeneousBlockMass p s M v k ≤ c)
    (hagrad : homogeneousBlockMass p s (M + b - 1) a k = c) : False := by
  have hlt := lower_positive_and_zero_block_lt hp hM hb hr hv hva ha k
    (by rwa [hvgrad]) (by rwa [hvgrad])
  rw [hvgrad, hagrad] at hlt
  exact lt_irrefl _ hlt

end

end PoissonBinomialComparison
