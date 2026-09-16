import PoissonBinomialComparison.SwitchRatioDerivative
import PoissonBinomialComparison.ContinuousSwitchGeometry

/-!
# Monotonicity of switch geometry

The proved centering inequalities give strict decrease of `R` in the count ratio
up to the center. Reflection gives the sign of the gap-derivative correction in
both halves, proving the manuscript's bound `R' ≤ 2R/γ`.
-/

namespace PoissonBinomialComparison

/-- The product of the two centering expressions is nonnegative in either half. -/
theorem IsContinuousSwitch.centering_product_nonneg {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) :
    0 ≤ (a + b - 2 * c) *
      ((1 - 2 * c) * ((a - c) * (c - b) / (c * (1 - c))) - (a + b - 2 * c)) := by
  by_cases hc : c ≤ 1 / 2
  · exact mul_nonneg (h.additive_centering_nonneg hc) (h.geometric_centering_nonneg hc)
  · have hc' : 1 - c ≤ 1 / 2 := by linarith
    have hp := mul_nonneg (h.reflect.additive_centering_nonneg hc')
      (h.reflect.geometric_centering_nonneg hc')
    convert hp using 1
    ring

/-- The count-ratio derivative of `R` is strictly negative to the left of the center. -/
theorem deriv_continuousSwitchRatio_count_neg {c γ : ℝ} (hc0 : 0 < c) (hc2 : c < 1 / 2)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (fun d ↦ continuousSwitchRatio d γ) c < 0 := by
  have hc1 : c < 1 := by linarith
  rw [(hasDerivAt_continuousSwitchRatio_count hc0 hc1 hγ0 hγ1).deriv]
  have hs := continuousSwitchPair_spec hc0 hc1 hγ0 hγ1
  have he := hs.additive_centering_pos hc2
  have hz := hs.geometric_centering_nonneg hc2.le
  have ht := deriv_continuousSwitchLower_count_pos hc0 hc1 hγ0 hγ1
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (add_pos_of_nonneg_of_pos hz (mul_pos he ht)))
    (mul_pos hc0 (sub_pos.mpr hc1))

/-- At fixed gap, `R` strictly decreases in the count ratio through the central ratio. -/
theorem continuousSwitchRatio_strictAntiOn {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictAntiOn (fun c ↦ continuousSwitchRatio c γ) (Set.Ioc 0 (1 / 2 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (1 / 2 : ℝ))
  · intro c hc
    exact (hasDerivAt_continuousSwitchRatio_count hc.1 (by linarith [hc.2]) hγ0 hγ1).continuousAt.continuousWithinAt
  · intro c hc
    rw [interior_Ioc] at hc
    exact deriv_continuousSwitchRatio_count_neg hc.1 hc.2 hγ0 hγ1

/-- The manuscript's strict geometric ordering of discrete switch indices. -/
theorem switchRatio_strict_order {n i j : ℕ} (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 2)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) : switchRatio n j γ < switchRatio n i γ := by
  have hj0 : 0 < j := by omega
  have hjn : j < n := by omega
  have hin : i < n := by omega
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hjn2 : (2 : ℝ) * j ≤ n := by exact_mod_cast (show 2 * j ≤ n by omega)
  have hci0 : (0 : ℝ) < (i : ℝ) / n := div_pos (by exact_mod_cast hi) hn
  have hcj0 : (0 : ℝ) < (j : ℝ) / n := div_pos (by exact_mod_cast hj0) hn
  have hcj2 : (j : ℝ) / n ≤ 1 / 2 := (div_le_iff₀ hn).2 (by linarith)
  have hcij : (i : ℝ) / n < (j : ℝ) / n :=
    (div_lt_div_iff_of_pos_right hn).2 (by exact_mod_cast hij)
  have h := (continuousSwitchRatio_strictAntiOn hγ0 hγ1) ⟨hci0, le_trans hcij.le hcj2⟩
    ⟨hcj0, hcj2⟩ hcij
  simpa only [continuousSwitchRatio_at_ratio hi hin hγ0 hγ1,
    continuousSwitchRatio_at_ratio hj0 hjn hγ0 hγ1] using h

/-- The gap derivative bound `R' ≤ 2R/γ`, in both count-ratio halves. -/
theorem deriv_switchRatio_le {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (switchRatio n j) γ ≤ 2 * switchRatio n j γ / γ := by
  rw [deriv_switchRatio_gap hj hjn hγ0 hγ1]
  apply sub_le_self
  have hs := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have hcont := (isSwitch_iff_isContinuousSwitch hj hjn γ _ _).mp hs
  have hprod := hcont.centering_product_nonneg
  have hv : 0 < ((j : ℝ) / n) * (1 - (j : ℝ) / n) :=
    mul_pos (lt_trans hs.1 hc.1) (by linarith [hc.2, hs.2.2.1])
  exact div_nonneg hprod (mul_pos (mul_pos hγ0 hv)
    (sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2)).le

end PoissonBinomialComparison
