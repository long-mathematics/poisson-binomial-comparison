import PoissonBinomialComparison.ContinuousSwitch
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Centering inequalities for real-ratio switches

The manuscript's paired-logit inequalities are proved by two equivalent
reflection comparisons of the logarithmic height. Additive reflection about
`c` controls `a+b-2c`; reflection in log-odds about `logit(c)` controls the
product inequality. Both comparisons reduce to rational derivative signs.
-/

namespace PoissonBinomialComparison

noncomputable section

/-- Logarithmic height strictly decreases to the right of its mode `c`. -/
theorem continuousSwitchLogHeight_strictAntiOn {c : ℝ} (hc : 0 < c) :
    StrictAntiOn (continuousSwitchLogHeight c) (Set.Ioo c 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo c 1)
  · intro x hx
    exact (hasStrictDerivAt_continuousSwitchLogHeight c (hc.trans hx.1) hx.2).hasDerivAt.continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo c 1 := interior_subset hx
    rw [(hasStrictDerivAt_continuousSwitchLogHeight c (hc.trans hx'.1) hx'.2).hasDerivAt.deriv]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hx'.1)
      (mul_pos (hc.trans hx'.1) (sub_pos.mpr hx'.2))

private theorem additive_reflection_height_pos {c b : ℝ}
    (_hc0 : 0 < c) (hc1 : c < 1 / 2) (hb0 : 0 < b) (hbc : b < c) :
    0 < continuousSwitchLogHeight c (2 * c - b) - continuousSwitchLogHeight c b := by
  let G : ℝ → ℝ := fun x ↦ continuousSwitchLogHeight c (2 * c - x) - continuousSwitchLogHeight c x
  have hbounds (x : ℝ) (hx : x ∈ Set.Icc b c) :
      (0 < x ∧ x < 1) ∧ (0 < 2 * c - x ∧ 2 * c - x < 1) := by
    constructor <;> constructor <;> linarith [hx.1, hx.2]
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc b c) :
      HasDerivAt G ((c - x) / ((2 * c - x) * (1 - (2 * c - x))) -
        (c - x) / (x * (1 - x))) x := by
    obtain ⟨hxb, hAb⟩ := hbounds x hx
    have hd := (((hasStrictDerivAt_continuousSwitchLogHeight c hAb.1 hAb.2).hasDerivAt).comp x
      ((hasDerivAt_const x (2 * c)).sub (hasDerivAt_id x))).sub
      (hasStrictDerivAt_continuousSwitchLogHeight c hxb.1 hxb.2).hasDerivAt
    convert hd using 1
    · rfl
    · simp only [zero_sub]
      congr 1
      ring
  have hanti : StrictAntiOn G (Set.Icc b c) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc b c)
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxb := hbounds x ⟨hx.1.le, hx.2.le⟩
      rw [(hderiv x ⟨hx.1.le, hx.2.le⟩).deriv]
      apply sub_neg.mpr
      apply div_lt_div_of_pos_left (sub_pos.mpr hx.2)
        (mul_pos hxb.1.1 (sub_pos.mpr hxb.1.2))
      have hprod := mul_pos (sub_pos.mpr hx.2) (show 0 < 1 - 2 * c by linarith)
      nlinarith
  have hcmp := hanti ⟨le_rfl, hbc.le⟩ ⟨hbc.le, le_rfl⟩ hbc
  have hGc : G c = 0 := by simp [G, show 2 * c - c = c by ring]
  simpa only [hGc, G] using hcmp

/-- Strict additive centering: below ratio one half, the upper displacement
from the mode exceeds the lower displacement. -/
theorem IsContinuousSwitch.additive_centering_pos {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) (hc : c < 1 / 2) : 0 < a + b - 2 * c := by
  have hcb := h.center_bounds
  have hc0 := h.1.trans hcb.1
  have hcmp := additive_reflection_height_pos hc0 hc h.1 hcb.1
  have href : 2 * c - b < a := by
    by_contra hn
    have haR : a ≤ 2 * c - b := le_of_not_gt hn
    have hmono := (continuousSwitchLogHeight_strictAntiOn hc0).antitoneOn
      ⟨hcb.2, h.2.2.1⟩ ⟨by linarith [hcb.1], by linarith [h.1]⟩ haR
    rw [h.2.2.2.2] at hmono
    linarith
  linarith

private def oddsReflection (c x : ℝ) : ℝ :=
  c ^ 2 * (1 - x) / (c ^ 2 + (1 - 2 * c) * x)

private theorem oddsReflection_bounds {c x : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 2)
    (hx0 : 0 < x) (hxc : x ≤ c) :
    0 < oddsReflection c x ∧ oddsReflection c x < 1 := by
  have hx1 : x < 1 := by linarith
  have hD : 0 < c ^ 2 + (1 - 2 * c) * x := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hc0)
      (mul_nonneg (by linarith) hx0.le)
  refine ⟨div_pos (mul_pos (sq_pos_of_pos hc0) (sub_pos.mpr hx1)) hD, ?_⟩
  apply (div_lt_one hD).mpr
  have hpos := mul_pos (sq_pos_of_pos (show 0 < 1 - c by linarith)) hx0
  nlinarith

private theorem oddsReflection_gt_center {c x : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 2)
    (hx0 : 0 < x) (hxc : x < c) : c < oddsReflection c x := by
  have hD : 0 < c ^ 2 + (1 - 2 * c) * x := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hc0)
      (mul_nonneg (by linarith) hx0.le)
  apply (lt_div_iff₀ hD).mpr
  have hpos := mul_pos (mul_pos hc0 (show 0 < 1 - c by linarith)) (sub_pos.mpr hxc)
  nlinarith

private theorem oddsReflection_center {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 2) :
    oddsReflection c c = c := by
  have hD : c ^ 2 + (1 - 2 * c) * c ≠ 0 := by
    have hpos := mul_pos hc0 (show 0 < 1 - c by linarith)
    nlinarith
  unfold oddsReflection
  apply (div_eq_iff hD).mpr
  ring

private theorem odds_reflection_height_neg {c b : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1 / 2) (hb0 : 0 < b) (hbc : b < c) :
    continuousSwitchLogHeight c (oddsReflection c b) - continuousSwitchLogHeight c b < 0 := by
  let G : ℝ → ℝ := fun x ↦ continuousSwitchLogHeight c (oddsReflection c x) - continuousSwitchLogHeight c x
  have hD (x : ℝ) (hx : x ∈ Set.Icc b c) : 0 < c ^ 2 + (1 - 2 * c) * x := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hc0)
      (mul_nonneg (by linarith) (hb0.le.trans hx.1))
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc b c) :
      HasDerivAt G ((1 - 2 * c) * (x - c) ^ 2 /
        ((c ^ 2 + (1 - 2 * c) * x) * x * (1 - x))) x := by
    have hx0 := hb0.trans_le hx.1
    have hx1 : x < 1 := by linarith [hx.2]
    have hR := oddsReflection_bounds hc0 hc1 hx0 hx.2
    have hnum := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).const_mul (c ^ 2)
    have hden := (hasDerivAt_const x (c ^ 2)).add ((hasDerivAt_id x).const_mul (1 - 2 * c))
    have hRderiv := hnum.div hden (hD x hx).ne'
    have hd := (((hasStrictDerivAt_continuousSwitchLogHeight c hR.1 hR.2).hasDerivAt).comp x
      hRderiv).sub (hasStrictDerivAt_continuousSwitchLogHeight c hx0 hx1).hasDerivAt
    convert hd using 1
    · rfl
    · dsimp only [Pi.sub_apply, Pi.add_apply, id_eq]
      have hc1' : 1 - c ≠ 0 := by linarith
      have hx1' := (sub_pos.mpr hx1).ne'
      have hDn := (hD x hx).ne'
      have hN : c ^ 2 + (1 - 2 * c) * x - c ^ 2 * (1 - x) ≠ 0 := by
        have hp := mul_pos hx0 (sq_pos_of_ne_zero hc1')
        nlinarith
      unfold oddsReflection
      field_simp [hN]
      ring
  have hmono : StrictMonoOn G (Set.Icc b c) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc b c)
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x ⟨hx.1.le, hx.2.le⟩).deriv]
      exact div_pos (mul_pos (by linarith) (sq_pos_of_ne_zero (sub_ne_zero.mpr hx.2.ne)))
        (mul_pos (mul_pos (hD x ⟨hx.1.le, hx.2.le⟩) (hb0.trans hx.1)) (by linarith [hx.2]))
  have hcmp := hmono ⟨le_rfl, hbc.le⟩ ⟨hbc.le, le_rfl⟩ hbc
  have hGc : G c = 0 := by simp only [G, oddsReflection_center hc0 hc1, sub_self]
  simpa only [hGc, G] using hcmp

/-- Strict log-odds centering, expressed without logarithms or square roots.
This is the manuscript's strict `c²(1-a)(1-b) > (1-c)²ab` inequality. -/
theorem IsContinuousSwitch.odds_centering_pos {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) (hc : c < 1 / 2) :
    0 < c ^ 2 * (1 - a) * (1 - b) - (1 - c) ^ 2 * a * b := by
  have hcb := h.center_bounds
  have hc0 := h.1.trans hcb.1
  have hcmp := odds_reflection_height_neg hc0 hc h.1 hcb.1
  have hR := oddsReflection_bounds hc0 hc h.1 hcb.1.le
  have haR : a < oddsReflection c b := by
    by_contra hn
    have hRa : oddsReflection c b ≤ a := le_of_not_gt hn
    have hmono := (continuousSwitchLogHeight_strictAntiOn hc0).antitoneOn
      ⟨oddsReflection_gt_center hc0 hc h.1 hcb.1, hR.2⟩ ⟨hcb.2, h.2.2.1⟩ hRa
    rw [h.2.2.2.2] at hmono
    linarith
  have hD : 0 < c ^ 2 + (1 - 2 * c) * b := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hc0) (mul_nonneg (by linarith) h.1.le)
  have hmul := (lt_div_iff₀ hD).mp haR
  nlinarith

/-- At count ratio one half the switch parameters are complementary. -/
theorem IsContinuousSwitch.sum_eq_one_of_half {γ a b : ℝ}
    (h : IsContinuousSwitch (1 / 2) γ a b) : a + b = 1 := by
  have hγ : 0 < γ := by linarith [h.2.1, h.2.2.2.1]
  have href : IsContinuousSwitch (1 / 2) γ (1 - b) (1 - a) := by
    convert h.reflect using 1
    norm_num
  have heq := continuousSwitch_unique (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hγ h href
  linarith [heq.1]

/-- The manuscript's nonnegative additive displacement for ratios at most one half. -/
theorem IsContinuousSwitch.additive_centering_nonneg {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) (hc : c ≤ 1 / 2) : 0 ≤ a + b - 2 * c := by
  rcases lt_or_eq_of_le hc with hlt | heq
  · exact (h.additive_centering_pos hlt).le
  · subst c
    linarith [h.sum_eq_one_of_half]

/-- The manuscript's nonnegative log-odds centering inequality for ratios at most one half. -/
theorem IsContinuousSwitch.odds_centering_nonneg {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) (hc : c ≤ 1 / 2) :
    0 ≤ c ^ 2 * (1 - a) * (1 - b) - (1 - c) ^ 2 * a * b := by
  rcases lt_or_eq_of_le hc with hlt | heq
  · exact (h.odds_centering_pos hlt).le
  · subst c
    have hs := h.sum_eq_one_of_half
    nlinarith

/-- Algebraic equivalence between the odds-centering numerator and `v(zR-e)`. -/
theorem continuousSwitch_odds_centering_identity (c a b : ℝ) :
    c ^ 2 * (1 - a) * (1 - b) - (1 - c) ^ 2 * a * b =
      (1 - 2 * c) * (a - c) * (c - b) - (a + b - 2 * c) * c * (1 - c) := by
  ring

/-- The manuscript's geometric form `zR-e ≥ 0` of the log-odds inequality. -/
theorem IsContinuousSwitch.geometric_centering_nonneg {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) (hc : c ≤ 1 / 2) :
    0 ≤ (1 - 2 * c) * ((a - c) * (c - b) / (c * (1 - c))) - (a + b - 2 * c) := by
  have hc0 := h.1.trans h.center_bounds.1
  have hv : 0 < c * (1 - c) := mul_pos hc0 (by linarith)
  have heq : c * (1 - c) *
      ((1 - 2 * c) * ((a - c) * (c - b) / (c * (1 - c))) - (a + b - 2 * c)) =
      c ^ 2 * (1 - a) * (1 - b) - (1 - c) ^ 2 * a * b := by
    rw [continuousSwitch_odds_centering_identity]
    have hc1 : 1 - c ≠ 0 := by linarith
    field_simp
  have hm : 0 ≤ c * (1 - c) *
      ((1 - 2 * c) * ((a - c) * (c - b) / (c * (1 - c))) - (a + b - 2 * c)) := by
    rw [heq]
    exact h.odds_centering_nonneg hc
  exact nonneg_of_mul_nonneg_right hm hv

end

end PoissonBinomialComparison
