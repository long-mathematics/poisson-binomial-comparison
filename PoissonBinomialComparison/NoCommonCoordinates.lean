import PoissonBinomialComparison.HomogeneousBlockMode

/-!
# The scalar obstruction to an unchanged block

The fixed law on `s` is the common block. The extra coordinate `z`, with parameter
`w`, is the randomizing Bernoulli variable in the free-coordinate gradient.
Strict unimodality and likelihood-ratio order contradict the two nonnegative
common-coordinate multipliers. The equality of the multipliers is unnecessary.
-/

namespace PoissonBinomialComparison

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- Equal positive free gradients for two interior homogeneous blocks are
incompatible with nonnegative common-coordinate multipliers. -/
theorem homogeneous_blocks_common_multiplier_impossible
    {p : ι → ℝ} {s : Finset ι} {z : ι} (hz : z ∉ s)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b w : ℝ}
    (hb0 : 0 < b) (hba : b < a) (ha1 : a < 1)
    (hw0 : 0 < w) (hw1 : w < 1) (hpz : p z = w) (k : ℤ)
    (hbprev : 0 < homogeneousBlockMass p s (M+2) b (k-1))
    (hbk : 0 < homogeneousBlockMass p s (M+2) b k)
    (heq : homogeneousBlockMass p (insert z s) (M+2) b k =
      homogeneousBlockMass p (insert z s) (M+2) a k)
    (hνa : 0 ≤ (a-w) * (homogeneousBlockMass p s (M+2) a (k-1) -
      homogeneousBlockMass p s (M+2) a k))
    (hνb : 0 ≤ (b-w) * (homogeneousBlockMass p s (M+2) b (k-1) -
      homogeneousBlockMass p s (M+2) b k)) : False := by
  have ha : 0 < a ∧ a < 1 := ⟨hb0.trans hba,ha1⟩
  have hb : 0 < b ∧ b < 1 := ⟨hb0,hba.trans ha1⟩
  have hps : ∀ i ∈ insert z s, 0 ≤ p i ∧ p i ≤ 1 := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · rw [hpz]; exact ⟨hw0.le,hw1.le⟩
    · exact hp i hi
  have hapos := (homogeneousBlockMass_pos_iff hp (M+2) hb ha k).mp hbk
  have hgpos : 0 < homogeneousBlockMass p (insert z s) (M+2) b k := by
    rw [homogeneousBlockMass_insert p hz,hpz]
    exact add_pos (mul_pos (sub_pos.mpr hw1) hbk) (mul_pos hw0 hbprev)
  obtain ⟨u,hbu,hua,hupos,hdu⟩ := homogeneousBlockMass_exists_critical_between
    hps (M+2) hb0 hba ha1 k hgpos heq
  have hu : 0 < u ∧ u < 1 := ⟨hb0.trans hbu,hua.trans ha1⟩
  have hda := homogeneousBlockMass_deriv_neg_after_critical hps M hu ⟨hua,ha1⟩ k hupos hdu
  have hdb := homogeneousBlockMass_deriv_pos_before_critical hps M hu ⟨hb0,hbu⟩ k hupos hdu
  rw [show M+2 = (M+1)+1 by omega,deriv_homogeneousBlockMass_succ] at hda hdb
  have hDa : homogeneousBlockMass p (insert z s) (M+1) a (k-1) <
      homogeneousBlockMass p (insert z s) (M+1) a k := by
    have hM : (0 : ℝ) < (M+1+1 : ℕ) := by positivity
    nlinarith
  have hDb : homogeneousBlockMass p (insert z s) (M+1) b k <
      homogeneousBlockMass p (insert z s) (M+1) b (k-1) := by
    have hM : (0 : ℝ) < (M+1+1 : ℕ) := by positivity
    nlinarith
  rcases le_or_gt w b with hwb | hbw
  · have hwa : w < a := hwb.trans_lt hba
    have hA : homogeneousBlockMass p s (M+2) a k ≤
        homogeneousBlockMass p s (M+2) a (k-1) := by
      nlinarith
    have hlr := bernoulliConvolve_likelihoodRatio
      (homogeneousBlockMass_cross hp (M+1) ⟨ha.1.le,ha.2.le⟩) hwa.le (k-1) k (by omega)
    have hDa0 := homogeneousBlockMass_nonneg hps (M+1) ⟨ha.1.le,ha.2.le⟩ (k-1)
    have hDa1 : 0 < homogeneousBlockMass p (insert z s) (M+1) a k := hDa0.trans_lt hDa
    have hform (l : ℤ) : bernoulliConvolve (homogeneousBlockMass p s (M+1) a) w l =
        homogeneousBlockMass p (insert z s) (M+1) a l := by
      simp only [homogeneousBlockMass_insert p hz,hpz,bernoulliConvolve]
    rw [hform,hform] at hlr
    change homogeneousBlockMass p s (M+2) a (k-1) *
      homogeneousBlockMass p (insert z s) (M+1) a k ≤
      homogeneousBlockMass p s (M+2) a k *
      homogeneousBlockMass p (insert z s) (M+1) a (k-1) at hlr
    nlinarith only [hlr, mul_pos (sub_pos.mpr hDa) hapos,
      mul_nonneg hDa1.le (sub_nonneg.mpr hA)]
  · rcases le_or_gt a w with haw | hwa
    · have hbw' : b < w := hba.trans_le haw
      have hB : homogeneousBlockMass p s (M+2) b (k-1) ≤
          homogeneousBlockMass p s (M+2) b k := by nlinarith
      have hlr := bernoulliConvolve_likelihoodRatio
        (homogeneousBlockMass_cross hp (M+1) ⟨hb.1.le,hb.2.le⟩) hbw'.le (k-1) k (by omega)
      have hform (l : ℤ) : bernoulliConvolve (homogeneousBlockMass p s (M+1) b) w l =
          homogeneousBlockMass p (insert z s) (M+1) b l := by
        simp only [homogeneousBlockMass_insert p hz,hpz,bernoulliConvolve]
      rw [hform,hform] at hlr
      change homogeneousBlockMass p (insert z s) (M+1) b (k-1) *
        homogeneousBlockMass p s (M+2) b k ≤
        homogeneousBlockMass p (insert z s) (M+1) b k *
        homogeneousBlockMass p s (M+2) b (k-1) at hlr
      have hDb0 := homogeneousBlockMass_nonneg hps (M+1) ⟨hb.1.le,hb.2.le⟩ k
      nlinarith only [hlr, mul_pos (sub_pos.mpr hDb) hbk, mul_nonneg hDb0 (sub_nonneg.mpr hB)]
    · have hA : homogeneousBlockMass p s (M+2) a k ≤
          homogeneousBlockMass p s (M+2) a (k-1) := by nlinarith
      have hB : homogeneousBlockMass p s (M+2) b (k-1) ≤
          homogeneousBlockMass p s (M+2) b k := by nlinarith
      have hstrict := homogeneousBlockMass_strict_adjacent hp (M+1)
        ⟨hb.1.le,hb.2.le⟩ ⟨ha.1.le,ha.2.le⟩ hba (k-1) hbprev
        (by simpa using hbk) (by simpa using hapos)
      simp only [sub_add_cancel] at hstrict
      nlinarith only [hstrict, mul_nonneg hapos.le (sub_nonneg.mpr hB),
        mul_nonneg hbk.le (sub_nonneg.mpr hA)]

end PoissonBinomialComparison
