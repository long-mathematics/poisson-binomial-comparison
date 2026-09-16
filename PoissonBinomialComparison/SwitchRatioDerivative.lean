import PoissonBinomialComparison.ContinuousSwitchDerivative

/-!
# Gap derivatives of the switch geometry

The gap derivative of `R` is written as `2R/γ` minus a geometric correction.
The sign of that correction is supplied separately by the centering inequalities.
-/

namespace PoissonBinomialComparison

/-- The continuous-ratio geometry agrees with the original geometry at `c=j/n`. -/
theorem continuousSwitchRatio_at_ratio {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    continuousSwitchRatio ((j : ℝ) / n) γ = switchRatio n j γ := by
  obtain ⟨ha, hb⟩ := continuousSwitch_at_ratio hj hjn hγ0 hγ1
  simp only [continuousSwitchRatio, switchRatio, ha, hb]

private theorem ratio_gap_derivative_algebra {a b c γ v R : ℝ}
    (hγ : γ ≠ 0) (hv : v ≠ 0) (hR : 1 - R ≠ 0)
    (hvv : v = c * (1 - c)) (hRv : R * v = (a - c) * (c - b)) :
    (((c - b) * a * (1 - a) / (γ * v * (1 - R))) * (c - b) -
      (a - c) * (-(a - c) * b * (1 - b) / (γ * v * (1 - R)))) / v =
      2 * R / γ - (a + b - 2 * c) * ((1 - 2 * c) * R - (a + b - 2 * c)) /
        (γ * v * (1 - R)) := by
  field_simp
  rw [hvv] at hRv ⊢
  linear_combination (2 * R * (c * (1 - c)) - 2 * a * b + a + b - 4 * (c * (1 - c))) * hRv

/-- The gap derivative of `R`, with its exact geometric correction term. -/
theorem hasDerivAt_switchRatio_gap {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let c := (j : ℝ) / n
    let e := switchUpper n j γ + switchLower n j γ - 2 * c
    HasDerivAt (switchRatio n j)
      (2 * switchRatio n j γ / γ -
        e * ((1 - 2 * c) * switchRatio n j γ - e) /
          (γ * (c * (1 - c)) * (1 - switchRatio n j γ))) γ := by
  let a := switchUpper n j γ
  let b := switchLower n j γ
  let c := (j : ℝ) / n
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have hv : c * (1 - c) ≠ 0 :=
    (mul_pos (lt_trans hs.1 hc.1) (by linarith [hc.2, hs.2.2.1])).ne'
  have hR : 1 - (a - c) * (c - b) / (c * (1 - c)) ≠ 0 :=
    (sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2).ne'
  have hA := (differentiableAt_switchUpper hj hjn hγ0 hγ1).hasDerivAt
  have hB := (differentiableAt_switchLower hj hjn hγ0 hγ1).hasDerivAt
  have hd := ((hA.sub_const c).mul ((hasDerivAt_const γ c).sub hB)).div_const (c * (1 - c))
  convert hd using 1
  · rfl
  · rw [deriv_switchUpper hj hjn hγ0 hγ1, deriv_switchLower hj hjn hγ0 hγ1]
    have hRv : switchRatio n j γ * (c * (1 - c)) = (a - c) * (c - b) := div_mul_cancel₀ _ hv
    convert (ratio_gap_derivative_algebra hγ0.ne' hv hR rfl hRv).symm using 1 <;>
      dsimp [a, b, c, switchRatio]
    ring

/-- A rewriting interface for the exact gap derivative of `R`. -/
theorem deriv_switchRatio_gap {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let c := (j : ℝ) / n
    let e := switchUpper n j γ + switchLower n j γ - 2 * c
    deriv (switchRatio n j) γ =
      2 * switchRatio n j γ / γ -
        e * ((1 - 2 * c) * switchRatio n j γ - e) /
          (γ * (c * (1 - c)) * (1 - switchRatio n j γ)) :=
  (hasDerivAt_switchRatio_gap hj hjn hγ0 hγ1).deriv

end PoissonBinomialComparison
