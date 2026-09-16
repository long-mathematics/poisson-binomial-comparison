import PoissonBinomialComparison.ContinuousSwitch
import PoissonBinomialComparison.SwitchDerivative

/-!
# Differentiating the continuous count ratio

The count-ratio derivatives follow from the scalar implicit function theorem
applied to the logarithmic equal-height equation, with the coordinate gap fixed.
-/

namespace PoissonBinomialComparison

open Filter
open scoped Topology

private theorem logarithmic_equation_hasStrictFDerivAt {c γ b : ℝ}
    (hb0 : 0 < b) (ha0 : 0 < γ + b) (ha1 : γ + b < 1) (hb1 : b < 1) :
    HasStrictFDerivAt
      (fun z : ℝ × ℝ ↦ continuousSwitchLogHeight z.1 (γ + z.2) - continuousSwitchLogHeight z.1 z.2)
      ((Real.log (γ + b) - Real.log b - Real.log (1 - (γ + b)) + Real.log (1 - b)) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        ((c - (γ + b)) / ((γ + b) * (1 - (γ + b))) - (c - b) / (b * (1 - b))) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) (c, b) := by
  have hS : HasStrictFDerivAt (fun z : ℝ × ℝ ↦ z.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (c, b) := hasStrictFDerivAt_snd
  have hA := (Real.hasStrictDerivAt_log ha0.ne').comp_hasStrictFDerivAt (c, b)
    ((hasStrictFDerivAt_const γ (c, b)).add hS)
  have hB := (Real.hasStrictDerivAt_log hb0.ne').comp_hasStrictFDerivAt (c, b) hS
  have hA1 := (Real.hasStrictDerivAt_log (sub_pos.mpr ha1).ne').comp_hasStrictFDerivAt (c, b)
    ((hasStrictFDerivAt_const (1 : ℝ) (c, b)).sub
      ((hasStrictFDerivAt_const γ (c, b)).add hS))
  have hB1 := (Real.hasStrictDerivAt_log (sub_pos.mpr hb1).ne').comp_hasStrictFDerivAt (c, b)
    ((hasStrictFDerivAt_const (1 : ℝ) (c, b)).sub hS)
  have hC : HasStrictFDerivAt (fun z : ℝ × ℝ ↦ z.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (c, b) := hasStrictFDerivAt_fst
  have hC1 := (hasStrictFDerivAt_const (1 : ℝ) (c, b)).sub hC
  have hd := ((hC.mul hA).add (hC1.mul hA1)).sub ((hC.mul hB).add (hC1.mul hB1))
  have ha1' : 1 - (γ + b) ≠ 0 := (sub_pos.mpr ha1).ne'
  have hb1' : 1 - b ≠ 0 := (sub_pos.mpr hb1).ne'
  convert hd using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro z
    simp
    field_simp [ha1', hb1', ha0.ne', hb0.ne']
    ring

/-- The derivative of the logarithmic switch equation in the lower parameter is negative. -/
theorem IsContinuousSwitch.lower_partial_neg {c γ a b : ℝ} (h : IsContinuousSwitch c γ a b) :
    (c - a) / (a * (1 - a)) - (c - b) / (b * (1 - b)) < 0 := by
  have hc := h.center_bounds
  have ha0 := lt_trans h.1 h.2.1
  have ha1 := sub_pos.mpr h.2.2.1
  have hb1 := sub_pos.mpr (lt_trans h.2.1 h.2.2.1)
  have hleft := div_neg_of_neg_of_pos (sub_neg.mpr hc.2) (mul_pos ha0 ha1)
  have hright := div_pos (sub_pos.mpr hc.1) (mul_pos h.1 hb1)
  linarith

/-- The derivative of the logarithmic switch equation in its count ratio is positive. -/
theorem IsContinuousSwitch.ratio_partial_pos {c γ a b : ℝ} (h : IsContinuousSwitch c γ a b) :
    0 < Real.log a - Real.log b - Real.log (1 - a) + Real.log (1 - b) := by
  have hlog := Real.log_lt_log h.1 h.2.1
  have hlog1 := Real.log_lt_log (sub_pos.mpr h.2.2.1) (by linarith [h.2.1] : 1 - a < 1 - b)
  linarith

/-- The lower endpoint is differentiable in the real count ratio, with its exact IFT derivative. -/
theorem hasDerivAt_continuousSwitchLower_count {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let a := continuousSwitchUpper c γ
    let b := continuousSwitchLower c γ
    HasDerivAt (fun d ↦ continuousSwitchLower d γ)
      (-(Real.log a - Real.log b - Real.log (1 - a) + Real.log (1 - b)) /
        ((c - a) / (a * (1 - a)) - (c - b) / (b * (1 - b)))) c := by
  let a := continuousSwitchUpper c γ
  let b := continuousSwitchLower c γ
  let A := Real.log a - Real.log b - Real.log (1 - a) + Real.log (1 - b)
  let B := (c - a) / (a * (1 - a)) - (c - b) / (b * (1 - b))
  let L : (ℝ × ℝ) →L[ℝ] ℝ := A • ContinuousLinearMap.fst ℝ ℝ ℝ + B • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hs : IsContinuousSwitch c γ a b := continuousSwitchPair_spec hc0 hc1 hγ0 hγ1
  have hab : γ + b = a := by linarith [hs.2.2.2.1]
  have hB : B ≠ 0 := hs.lower_partial_neg.ne
  have hF : HasStrictFDerivAt
      (fun z : ℝ × ℝ ↦ continuousSwitchLogHeight z.1 (γ + z.2) - continuousSwitchLogHeight z.1 z.2)
      L (c, b) := by
    simpa only [hab] using logarithmic_equation_hasStrictFDerivAt (c := c) (γ := γ)
      hs.1 (hab ▸ lt_trans hs.1 hs.2.1) (hab ▸ hs.2.2.1) (lt_trans hs.2.1 hs.2.2.1)
  have hL : L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ = B • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [L]
  have hL1 : L ∘L ContinuousLinearMap.inl ℝ ℝ ℝ = A • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [L]
  have hInv1 : (B • ContinuousLinearMap.id ℝ ℝ) ∘L (B⁻¹ • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [hB]
  have hInv2 : (B⁻¹ • ContinuousLinearMap.id ℝ ℝ) ∘L (B • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [hB]
  have hinv : (L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hL]
    exact ContinuousLinearMap.IsInvertible.of_inverse hInv1 hInv2
  let ψ := hF.implicitFunctionOfProdDomain hinv
  have hψd : HasDerivAt ψ (-A / B) c := by
    have hd := (hF.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.hasDerivAt
    rw [hL, hL1, ContinuousLinearMap.inverse_eq hInv1 hInv2] at hd
    simpa [ψ, div_eq_mul_inv, mul_comm] using hd
  have hψt : Tendsto ψ (𝓝 c) (𝓝 b) := hF.tendsto_implicitFunctionOfProdDomain hinv
  have hψeq := hF.eventually_apply_implicitFunctionOfProdDomain hinv
  have heq : (fun d ↦ continuousSwitchLower d γ) =ᶠ[𝓝 c] ψ := by
    have evb : ∀ᶠ d in 𝓝 c, 0 < ψ d := hψt.eventually (Ioi_mem_nhds hs.1)
    have eva : ∀ᶠ d in 𝓝 c, γ + ψ d < 1 :=
      (tendsto_const_nhds.add hψt).eventually (Iio_mem_nhds (hab ▸ hs.2.2.1))
    filter_upwards [hψeq, evb, eva, Ioo_mem_nhds hc0 hc1] with d hd hdb hda hdc
    have hdS : IsContinuousSwitch d γ (γ + ψ d) (ψ d) := by
      refine ⟨hdb, by linarith, hda, by ring, ?_⟩
      change continuousSwitchLogHeight d (γ + ψ d) - continuousSwitchLogHeight d (ψ d) =
        continuousSwitchLogHeight c (γ + b) - continuousSwitchLogHeight c b at hd
      rw [hab, hs.2.2.2.2, sub_self] at hd
      exact sub_eq_zero.mp hd
    exact (hdS.eq_continuousSwitchPair hdc.1 hdc.2).2.symm
  exact hψd.congr_of_eventuallyEq heq

/-- The upper and lower endpoint derivatives in the count ratio agree. -/
theorem hasDerivAt_continuousSwitchUpper_count {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    HasDerivAt (fun d ↦ continuousSwitchUpper d γ)
      (deriv (fun d ↦ continuousSwitchLower d γ) c) c := by
  have hd := (hasDerivAt_continuousSwitchLower_count hc0 hc1 hγ0 hγ1).differentiableAt.hasDerivAt
  have heq : (fun d ↦ continuousSwitchUpper d γ) =ᶠ[𝓝 c]
      (fun d ↦ γ + continuousSwitchLower d γ) := by
    filter_upwards [Ioo_mem_nhds hc0 hc1] with d hd
    have h := (continuousSwitchPair_spec hd.1 hd.2 hγ0 hγ1).2.2.2.1
    linarith
  simpa only [zero_add] using ((hasDerivAt_const c γ).add hd).congr_of_eventuallyEq heq

/-- Moving the switching count ratio to the right strictly increases its lower endpoint. -/
theorem deriv_continuousSwitchLower_count_pos {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    0 < deriv (fun d ↦ continuousSwitchLower d γ) c := by
  rw [(hasDerivAt_continuousSwitchLower_count hc0 hc1 hγ0 hγ1).deriv]
  have hs := continuousSwitchPair_spec hc0 hc1 hγ0 hγ1
  exact div_pos_of_neg_of_neg (neg_neg_of_pos hs.ratio_partial_pos) hs.lower_partial_neg

/-- Moving the switching count ratio to the right strictly increases its upper endpoint. -/
theorem deriv_continuousSwitchUpper_count_pos {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    0 < deriv (fun d ↦ continuousSwitchUpper d γ) c := by
  rw [(hasDerivAt_continuousSwitchUpper_count hc0 hc1 hγ0 hγ1).deriv]
  exact deriv_continuousSwitchLower_count_pos hc0 hc1 hγ0 hγ1

/-- The manuscript's count-ratio derivative of `R`, before applying the geometric signs. -/
theorem hasDerivAt_continuousSwitchRatio_count {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let e := continuousSwitchUpper c γ + continuousSwitchLower c γ - 2 * c
    let t := deriv (fun d ↦ continuousSwitchLower d γ) c
    HasDerivAt (fun d ↦ continuousSwitchRatio d γ)
      (-(((1 - 2 * c) * continuousSwitchRatio c γ - e) + e * t) / (c * (1 - c))) c := by
  let a := continuousSwitchUpper c γ
  let b := continuousSwitchLower c γ
  let t := deriv (fun d ↦ continuousSwitchLower d γ) c
  let v := c * (1 - c)
  let R := continuousSwitchRatio c γ
  have ha := hasDerivAt_continuousSwitchUpper_count hc0 hc1 hγ0 hγ1
  have hb := (hasDerivAt_continuousSwitchLower_count hc0 hc1 hγ0 hγ1).differentiableAt.hasDerivAt
  have hv : v ≠ 0 := (mul_pos hc0 (sub_pos.mpr hc1)).ne'
  have hd := (((ha.sub (hasDerivAt_id c)).mul ((hasDerivAt_id c).sub hb)).div
    ((hasDerivAt_id c).mul ((hasDerivAt_const c (1 : ℝ)).sub (hasDerivAt_id c))) hv)
  convert hd using 1
  · rfl
  · change -(((1 - 2 * c) * R - (a + b - 2 * c)) + (a + b - 2 * c) * t) / v =
      (((t - 1) * (c - b) + (a - c) * (1 - t)) * v -
        (a - c) * (c - b) * (1 * (1 - c) + c * (0 - 1))) / v ^ 2
    have hRv : R * v = (a - c) * (c - b) := div_mul_cancel₀ _ hv
    field_simp
    dsimp [v]
    linear_combination -(1 - 2 * c) * hRv

end PoissonBinomialComparison
