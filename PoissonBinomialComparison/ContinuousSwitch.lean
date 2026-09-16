import PoissonBinomialComparison.SwitchFunctions
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Switches with a real count ratio

The continuous count ratio `c` replaces `j/n`. Existence is proved with the
continuous height `x^c(1-x)^(1-c)`, whose endpoint values are finite. On interior
parameters its logarithm is the manuscript's logarithmic equal-height equation.
-/

namespace PoissonBinomialComparison

/-- Real-exponent height for a continuous count ratio. -/
noncomputable def continuousSwitchHeight (c x : ℝ) : ℝ :=
  x ^ c * (1 - x) ^ (1 - c)

/-- Logarithmic height for a continuous count ratio. -/
noncomputable def continuousSwitchLogHeight (c x : ℝ) : ℝ :=
  c * Real.log x + (1 - c) * Real.log (1 - x)

/-- A switch with real count ratio `c`, expressed by the logarithmic equation. -/
def IsContinuousSwitch (c γ a b : ℝ) : Prop :=
  0 < b ∧ b < a ∧ a < 1 ∧ a - b = γ ∧
    continuousSwitchLogHeight c a = continuousSwitchLogHeight c b

theorem continuousSwitchHeight_pos (c : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < continuousSwitchHeight c x :=
  mul_pos (Real.rpow_pos_of_pos hx0 c) (Real.rpow_pos_of_pos (sub_pos.mpr hx1) (1 - c))

/-- Logarithmic and real-power heights agree on interior parameters. -/
theorem log_continuousSwitchHeight (c : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log (continuousSwitchHeight c x) = continuousSwitchLogHeight c x := by
  rw [continuousSwitchHeight, Real.log_mul
    (Real.rpow_pos_of_pos hx0 c).ne'
    (Real.rpow_pos_of_pos (sub_pos.mpr hx1) (1 - c)).ne',
    Real.log_rpow hx0, Real.log_rpow (sub_pos.mpr hx1)]
  rfl

/-- Equality of logarithmic heights is equivalent to equality of positive heights. -/
theorem continuousSwitchHeight_eq_iff (c : ℝ) {a b : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    continuousSwitchHeight c a = continuousSwitchHeight c b ↔
      continuousSwitchLogHeight c a = continuousSwitchLogHeight c b := by
  constructor
  · intro h
    simpa only [log_continuousSwitchHeight c ha0 ha1,
      log_continuousSwitchHeight c hb0 hb1] using congrArg Real.log h
  · intro h
    apply Real.log_injOn_pos (continuousSwitchHeight_pos c ha0 ha1)
      (continuousSwitchHeight_pos c hb0 hb1)
    simpa only [log_continuousSwitchHeight c ha0 ha1,
      log_continuousSwitchHeight c hb0 hb1] using h

/-- The continuous-ratio switch exists for every interior ratio and gap. -/
theorem exists_continuousSwitch {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) : ∃ a b : ℝ, IsContinuousSwitch c γ a b := by
  let H : ℝ → ℝ := fun b ↦ continuousSwitchHeight c (b + γ) - continuousSwitchHeight c b
  have hc' : 0 < 1 - c := sub_pos.mpr hc1
  have hzero : continuousSwitchHeight c 0 = 0 := by
    simp [continuousSwitchHeight, Real.zero_rpow hc0.ne']
  have hone : continuousSwitchHeight c 1 = 0 := by
    simp [continuousSwitchHeight, Real.zero_rpow hc'.ne']
  have H0 : 0 < H 0 := by simpa [H, hzero] using continuousSwitchHeight_pos c hγ0 hγ1
  have H1 : H (1 - γ) < 0 := by
    have heq : 1 - γ + γ = 1 := by ring
    simp only [H, heq, hone, zero_sub, neg_neg_iff_pos]
    exact continuousSwitchHeight_pos c (by linarith) (by linarith)
  have hheight : Continuous (continuousSwitchHeight c) := by
    exact (Real.continuous_rpow_const hc0.le).mul
      ((Real.continuous_rpow_const hc'.le).comp (continuous_const.sub continuous_id))
  have hcont : ContinuousOn H (Set.Icc 0 (1 - γ)) :=
    ((hheight.comp (continuous_id.add continuous_const)).sub hheight).continuousOn
  obtain ⟨b, hb, heq⟩ := intermediate_value_Icc' (by linarith : 0 ≤ 1 - γ) hcont ⟨H1.le, H0.le⟩
  have hb0 : 0 < b := by
    apply lt_of_le_of_ne hb.1
    intro h
    subst b
    linarith
  have hb1 : b < 1 - γ := by
    apply lt_of_le_of_ne hb.2
    intro h
    rw [h] at heq
    linarith
  refine ⟨b + γ, b, hb0, by linarith, by linarith, by ring, ?_⟩
  exact (continuousSwitchHeight_eq_iff c (by linarith) (by linarith) hb0 (by linarith)).mp
    (sub_eq_zero.mp heq)

private theorem continuous_switch_ratio_strictAntiOn {c γ : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hγ : 0 < γ) :
    StrictAntiOn (fun b : ℝ ↦ ((b + γ) / b) ^ c *
      ((1 - (b + γ)) / (1 - b)) ^ (1 - c)) (Set.Ioo 0 (1 - γ)) := by
  intro b₁ hb₁ b₂ hb₂ hlt
  have hb₁' : 0 < 1 - b₁ := by linarith [hb₁.2]
  have hb₂' : 0 < 1 - b₂ := by linarith [hb₂.2]
  have hr₁ : (b₂ + γ) / b₂ < (b₁ + γ) / b₁ := by
    apply (div_lt_div_iff₀ hb₂.1 hb₁.1).2
    nlinarith
  have hr₂ : (1 - (b₂ + γ)) / (1 - b₂) < (1 - (b₁ + γ)) / (1 - b₁) := by
    apply (div_lt_div_iff₀ hb₂' hb₁').2
    nlinarith
  have hp₁ : 0 < (b₂ + γ) / b₂ := div_pos (by linarith [hb₂.1]) hb₂.1
  have hp₂ : 0 < (1 - (b₁ + γ)) / (1 - b₁) := div_pos (by linarith [hb₁.2]) hb₁'
  have hp₂' : 0 < (1 - (b₂ + γ)) / (1 - b₂) := div_pos (by linarith [hb₂.2]) hb₂'
  exact mul_lt_mul_of_pos (Real.rpow_lt_rpow hp₁.le hr₁ hc0)
    (Real.rpow_lt_rpow hp₂'.le hr₂ (sub_pos.mpr hc1))
    (Real.rpow_pos_of_pos hp₁ _) (Real.rpow_pos_of_pos hp₂ _)

private theorem continuous_switch_ratio_eq_one {c γ a b : ℝ} (h : IsContinuousSwitch c γ a b) :
    ((b + γ) / b) ^ c * ((1 - (b + γ)) / (1 - b)) ^ (1 - c) = 1 := by
  have ha0 : 0 < a := lt_trans h.1 h.2.1
  have hb1 : b < 1 := lt_trans h.2.1 h.2.2.1
  have hab : b + γ = a := by linarith [h.2.2.2.1]
  have heq := (continuousSwitchHeight_eq_iff c ha0 h.2.2.1 h.1 hb1).mpr h.2.2.2.2
  rw [hab, Real.div_rpow ha0.le h.1.le,
    Real.div_rpow (sub_nonneg.mpr h.2.2.1.le) (sub_nonneg.mpr hb1.le), div_mul_div_comm]
  change continuousSwitchHeight c a / continuousSwitchHeight c b = 1
  rw [heq, div_self (continuousSwitchHeight_pos c h.1 hb1).ne']

/-- The real-ratio equal-height equation determines both switch parameters uniquely. -/
theorem continuousSwitch_unique {c γ a₁ b₁ a₂ b₂ : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hγ : 0 < γ)
    (h₁ : IsContinuousSwitch c γ a₁ b₁) (h₂ : IsContinuousSwitch c γ a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hb₁ : b₁ ∈ Set.Ioo 0 (1 - γ) := ⟨h₁.1, by linarith [h₁.2.2.1, h₁.2.2.2.1]⟩
  have hb₂ : b₂ ∈ Set.Ioo 0 (1 - γ) := ⟨h₂.1, by linarith [h₂.2.2.1, h₂.2.2.2.1]⟩
  have heq := (continuous_switch_ratio_strictAntiOn hc0 hc1 hγ).injOn hb₁ hb₂
    ((continuous_switch_ratio_eq_one h₁).trans (continuous_switch_ratio_eq_one h₂).symm)
  exact ⟨by linarith [h₁.2.2.2.1, h₂.2.2.2.1], heq⟩

/-- Unique existence of the real-ratio switch. -/
theorem existsUnique_continuousSwitch {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) : ∃! ab : ℝ × ℝ, IsContinuousSwitch c γ ab.1 ab.2 := by
  obtain ⟨a, b, h⟩ := exists_continuousSwitch hc0 hc1 hγ0 hγ1
  refine ⟨(a, b), h, ?_⟩
  intro ab hab
  exact Prod.ext (continuousSwitch_unique hc0 hc1 hγ0 hab h).1
    (continuousSwitch_unique hc0 hc1 hγ0 hab h).2

/-- The continuous switch satisfies the manuscript's equation in log ratios. -/
theorem IsContinuousSwitch.log_ratio_eq_zero {c γ a b : ℝ} (h : IsContinuousSwitch c γ a b) :
    c * Real.log (a / b) + (1 - c) * Real.log ((1 - a) / (1 - b)) = 0 := by
  have ha0 : a ≠ 0 := (lt_trans h.1 h.2.1).ne'
  have ha1 : 1 - a ≠ 0 := (sub_pos.mpr h.2.2.1).ne'
  have hb1 : 1 - b ≠ 0 := (sub_pos.mpr (lt_trans h.2.1 h.2.2.1)).ne'
  rw [Real.log_div ha0 h.1.ne', Real.log_div ha1 hb1]
  have heq := h.2.2.2.2
  unfold continuousSwitchLogHeight at heq
  linarith

/-- Derivative of the logarithmic equal-height function. -/
theorem hasStrictDerivAt_continuousSwitchLogHeight (c : ℝ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasStrictDerivAt (continuousSwitchLogHeight c) ((c - x) / (x * (1 - x))) x := by
  have hx1' : 1 - x ≠ 0 := (sub_pos.mpr hx1).ne'
  have hd := ((Real.hasStrictDerivAt_log hx0.ne').const_mul c).add
    ((((hasStrictDerivAt_const x (1 : ℝ)).sub (hasStrictDerivAt_id x)).log hx1').const_mul (1 - c))
  convert hd using 1
  · rfl
  · dsimp only [Pi.sub_apply, id_eq]
    field_simp
    ring

/-- The real count ratio lies strictly between its switch parameters. -/
theorem IsContinuousSwitch.center_bounds {c γ a b : ℝ} (h : IsContinuousSwitch c γ a b) :
    b < c ∧ c < a := by
  have hcont : ContinuousOn (continuousSwitchLogHeight c) (Set.Icc b a) := by
    intro x hx
    exact (hasStrictDerivAt_continuousSwitchLogHeight c (lt_of_lt_of_le h.1 hx.1)
      (lt_of_le_of_lt hx.2 h.2.2.1)).hasDerivAt.continuousAt.continuousWithinAt
  obtain ⟨x, hx, hd⟩ := exists_hasDerivAt_eq_zero h.2.1 hcont h.2.2.2.2.symm
    (fun x hx ↦ (hasStrictDerivAt_continuousSwitchLogHeight c (lt_trans h.1 hx.1)
      (lt_trans hx.2 h.2.2.1)).hasDerivAt)
  have hx0 : 0 < x := lt_trans h.1 hx.1
  have hx1 : 0 < 1 - x := sub_pos.mpr (lt_trans hx.2 h.2.2.1)
  have hcx : c - x = 0 := (div_eq_zero_iff.mp hd).resolve_right (mul_pos hx0 hx1).ne'
  have hxc : x = c := by linarith
  exact hxc ▸ hx

/-- Complementation reflects the real count ratio about one half. -/
theorem IsContinuousSwitch.reflect {c γ a b : ℝ} (h : IsContinuousSwitch c γ a b) :
    IsContinuousSwitch (1 - c) γ (1 - b) (1 - a) := by
  refine ⟨by linarith [h.2.2.1], by linarith [h.2.1], by linarith [h.1],
    by linarith [h.2.2.2.1], ?_⟩
  have heq := h.2.2.2.2
  simp only [continuousSwitchLogHeight, sub_sub_cancel] at heq ⊢
  linarith

/-- Integer and real-ratio switch formulations are provably equivalent. -/
theorem isSwitch_iff_isContinuousSwitch {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    (γ a b : ℝ) : IsSwitch n j γ a b ↔ IsContinuousSwitch ((j : ℝ) / n) γ a b := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hlog (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
      a ^ j * (1 - a) ^ (n - j) = b ^ j * (1 - b) ^ (n - j) ↔
        continuousSwitchLogHeight ((j : ℝ) / n) a =
          continuousSwitchLogHeight ((j : ℝ) / n) b := by
    have hapos : 0 < a ^ j * (1 - a) ^ (n - j) :=
      mul_pos (pow_pos ha0 _) (pow_pos (sub_pos.mpr ha1) _)
    have hbpos : 0 < b ^ j * (1 - b) ^ (n - j) :=
      mul_pos (pow_pos hb0 _) (pow_pos (sub_pos.mpr hb1) _)
    have hlogA : Real.log (a ^ j * (1 - a) ^ (n - j)) =
        (j : ℝ) * Real.log a + ((n : ℝ) - j) * Real.log (1 - a) := by
      rw [Real.log_mul (pow_pos ha0 _).ne' (pow_pos (sub_pos.mpr ha1) _).ne',
        Real.log_pow, Real.log_pow, Nat.cast_sub hjn.le]
    have hlogB : Real.log (b ^ j * (1 - b) ^ (n - j)) =
        (j : ℝ) * Real.log b + ((n : ℝ) - j) * Real.log (1 - b) := by
      rw [Real.log_mul (pow_pos hb0 _).ne' (pow_pos (sub_pos.mpr hb1) _).ne',
        Real.log_pow, Real.log_pow, Nat.cast_sub hjn.le]
    constructor
    · intro heq
      have h := congrArg Real.log heq
      rw [hlogA, hlogB] at h
      unfold continuousSwitchLogHeight
      field_simp
      nlinarith only [h]
    · intro heq
      apply Real.log_injOn_pos hapos hbpos
      rw [hlogA, hlogB]
      unfold continuousSwitchLogHeight at heq
      field_simp at heq
      nlinarith only [heq]
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      (hlog (lt_trans h.1 h.2.1) h.2.2.1 h.1 (lt_trans h.2.1 h.2.2.1)).mp h.2.2.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      (hlog (lt_trans h.1 h.2.1) h.2.2.1 h.1 (lt_trans h.2.1 h.2.2.1)).mpr h.2.2.2.2⟩

/-- The canonical switch for a real count ratio, with constant endpoint extensions. -/
noncomputable def continuousSwitchPair (c γ : ℝ) : ℝ × ℝ :=
  if h : 0 < c ∧ c < 1 ∧ 0 < γ ∧ γ < 1 then
    Classical.choose (existsUnique_continuousSwitch h.1 h.2.1 h.2.2.1 h.2.2.2).exists
  else if γ ≤ 0 then (c, c) else (1, 0)

/-- Upper endpoint of the real-ratio switch. -/
noncomputable def continuousSwitchUpper (c γ : ℝ) : ℝ := (continuousSwitchPair c γ).1

/-- Lower endpoint of the real-ratio switch. -/
noncomputable def continuousSwitchLower (c γ : ℝ) : ℝ := (continuousSwitchPair c γ).2

/-- The real-ratio geometric quantity `R`. -/
noncomputable def continuousSwitchRatio (c γ : ℝ) : ℝ :=
  (continuousSwitchUpper c γ - c) * (c - continuousSwitchLower c γ) / (c * (1 - c))

/-- The selected real-ratio parameters satisfy the exact switch predicate. -/
theorem continuousSwitchPair_spec {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsContinuousSwitch c γ (continuousSwitchUpper c γ) (continuousSwitchLower c γ) := by
  have h : 0 < c ∧ c < 1 ∧ 0 < γ ∧ γ < 1 := ⟨hc0, hc1, hγ0, hγ1⟩
  simp only [continuousSwitchUpper, continuousSwitchLower, continuousSwitchPair, dite_eq_left h]
  exact Classical.choose_spec (existsUnique_continuousSwitch hc0 hc1 hγ0 hγ1).exists

/-- Any real-ratio switch equals the canonical pair. -/
theorem IsContinuousSwitch.eq_continuousSwitchPair {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) (hc0 : 0 < c) (hc1 : c < 1) :
    a = continuousSwitchUpper c γ ∧ b = continuousSwitchLower c γ := by
  have hγ0 : 0 < γ := by linarith [h.2.1, h.2.2.2.1]
  have hγ1 : γ < 1 := by linarith [h.1, h.2.2.1, h.2.2.2.1]
  exact continuousSwitch_unique hc0 hc1 hγ0 h (continuousSwitchPair_spec hc0 hc1 hγ0 hγ1)

/-- At rational count ratios the real-ratio construction is exactly the discrete switch. -/
theorem continuousSwitch_at_ratio {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    continuousSwitchUpper ((j : ℝ) / n) γ = switchUpper n j γ ∧
      continuousSwitchLower ((j : ℝ) / n) γ = switchLower n j γ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc0 : (0 : ℝ) < (j : ℝ) / n := div_pos (by exact_mod_cast hj) hn
  have hc1 : (j : ℝ) / n < 1 := (div_lt_one hn).2 (by exact_mod_cast hjn)
  have hs := (isSwitch_iff_isContinuousSwitch hj hjn γ _ _).mp (switchPair_spec hj hjn hγ0 hγ1)
  have heq := hs.eq_continuousSwitchPair hc0 hc1
  exact ⟨heq.1.symm, heq.2.symm⟩

/-- Reflection of the canonical real-ratio endpoints. -/
theorem continuousSwitchPair_reflection {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    continuousSwitchUpper (1 - c) γ = 1 - continuousSwitchLower c γ ∧
      continuousSwitchLower (1 - c) γ = 1 - continuousSwitchUpper c γ := by
  have h := ((continuousSwitchPair_spec hc0 hc1 hγ0 hγ1).reflect).eq_continuousSwitchPair
    (by linarith) (by linarith)
  exact ⟨h.1.symm, h.2.symm⟩

/-- The canonical real-ratio geometry satisfies `0<R<1`. -/
theorem continuousSwitchRatio_bounds {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    0 < continuousSwitchRatio c γ ∧ continuousSwitchRatio c γ < 1 := by
  have hs := continuousSwitchPair_spec hc0 hc1 hγ0 hγ1
  have hc := hs.center_bounds
  have hv : 0 < c * (1 - c) := mul_pos hc0 (sub_pos.mpr hc1)
  have ha0 := lt_trans hs.1 hs.2.1
  have ha1 := sub_pos.mpr hs.2.2.1
  have hb1 := sub_pos.mpr (lt_trans hs.2.1 hs.2.2.1)
  refine ⟨div_pos (mul_pos (sub_pos.mpr hc.2) (sub_pos.mpr hc.1)) hv, ?_⟩
  apply (div_lt_one hv).2
  have hid := switch_denominator_identity c (continuousSwitchUpper c γ) (continuousSwitchLower c γ)
  have hpos := add_pos (mul_pos (mul_pos hc0 ha1) hb1)
    (mul_pos (mul_pos (sub_pos.mpr hc1) ha0) hs.1)
  linarith

end PoissonBinomialComparison
