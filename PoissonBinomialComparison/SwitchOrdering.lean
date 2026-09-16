import PoissonBinomialComparison.SwitchMonotonicity
import PoissonBinomialComparison.SwitchIntegral

/-!
# Strict ordering of switching values

The comparison uses normalized positive densities with strictly ordered
logarithmic decay rates.  Their ratio decreases, so their difference changes
sign at most once.  Equal total integrals turn this single crossing into the
strict comparison of the switching objectives.
-/

namespace PoissonBinomialComparison

open Set MeasureTheory

private theorem decay_ratio_strictAntiOn {f g A B : ℝ → ℝ}
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (-A x * f x) x)
    (hg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g (-B x * g x) x)
    (hfp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < f x)
    (hgp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < g x)
    (hAB : ∀ x ∈ Ioo (0 : ℝ) 1, B x < A x) :
    StrictAntiOn (fun x ↦ f x / g x) (Ioo (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro x hx
    exact ((hf x hx).div (hg x hx) (hgp x hx).ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    change deriv (f / g) x < 0
    rw [((hf x hx).div (hg x hx) (hgp x hx).ne').deriv]
    apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (hgp x hx))
    have hp := mul_pos (sub_pos.mpr (hAB x hx)) (mul_pos (hfp x hx) (hgp x hx))
    nlinarith

/-- A normalized single-crossing comparison for the integral-minus-endpoint
functional appearing in the switch formula. -/
theorem integral_endpoint_strict_comparison {f g A B : ℝ → ℝ} {N γ : ℝ}
    (hN : 0 < N) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hfc : ContinuousOn f (Icc 0 1)) (hgc : ContinuousOn g (Icc 0 1))
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (-A x * f x) x)
    (hg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g (-B x * g x) x)
    (hfp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < f x)
    (hgp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < g x)
    (hBp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < B x)
    (hAB : ∀ x ∈ Ioo (0 : ℝ) 1, B x < A x)
    (hone : f 1 = g 1)
    (hnorm : (∫ x in (0 : ℝ)..1, f x) = ∫ x in (0 : ℝ)..1, g x) :
    (N + 1) * (∫ x in (0 : ℝ)..γ, g x) - γ * g γ <
      (N + 1) * (∫ x in (0 : ℝ)..γ, f x) - γ * f γ := by
  let h := fun x ↦ f x - g x
  have hc : ContinuousOn h (Icc 0 1) := hfc.sub hgc
  have hfi := hfc.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hgi := hgc.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hci := hc.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hsub : Icc (0 : ℝ) γ ⊆ Icc (0 : ℝ) 1 := fun x hx ↦ ⟨hx.1, hx.2.trans hγ1.le⟩
  have hsub' : Icc γ (1 : ℝ) ⊆ Icc (0 : ℝ) 1 := fun x hx ↦ ⟨hγ0.le.trans hx.1, hx.2⟩
  have hfiγ := (hfc.mono hsub).intervalIntegrable_of_Icc (μ := volume) hγ0.le
  have hgiγ := (hgc.mono hsub).intervalIntegrable_of_Icc (μ := volume) hγ0.le
  have hciγ := (hc.mono hsub).intervalIntegrable_of_Icc (μ := volume) hγ0.le
  have hciγ' := (hc.mono hsub').intervalIntegrable_of_Icc (μ := volume) hγ1.le
  have htotal : (∫ x in (0 : ℝ)..1, h x) = 0 := by
    rw [show h = fun x ↦ f x - g x from rfl, intervalIntegral.integral_sub hfi hgi, hnorm]
    ring
  have hr := decay_ratio_strictAntiOn hf hg hfp hgp hAB
  have hγmem : γ ∈ Ioo (0 : ℝ) 1 := ⟨hγ0, hγ1⟩
  have hgoal : 0 < (N + 1) * (∫ x in (0 : ℝ)..γ, h x) - γ * h γ := by
    by_cases hpos : 0 < h γ
    · have hpos_before : ∀ x ∈ Ioo (0 : ℝ) γ, 0 < h x := by
        intro x hx
        have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hγ1⟩
        have hrγ : 1 < f γ / g γ := (one_lt_div (hgp γ hγmem)).mpr (by dsimp [h] at hpos; linarith)
        have hrx := hr hx' hγmem hx.2
        have : g x < f x := (one_lt_div (hgp x hx')).mp (hrγ.trans hrx)
        dsimp [h]
        linarith
      have hanti : StrictAntiOn h (Icc (0 : ℝ) γ) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc 0 γ) (hc.mono hsub)
        intro x hx
        rw [interior_Icc] at hx
        have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hγ1⟩
        change deriv (f - g) x < 0
        rw [((hf x hx').sub (hg x hx')).deriv]
        have hAx : 0 < A x := (hBp x hx').trans (hAB x hx')
        have h1 := mul_pos hAx (hpos_before x hx)
        have h2 := mul_pos (sub_pos.mpr (hAB x hx')) (hgp x hx')
        dsimp [h] at h1
        nlinarith
      have hbound : γ * h γ ≤ ∫ x in (0 : ℝ)..γ, h x := by
        have hi := intervalIntegral.integral_mono_on hγ0.le
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ h γ) volume 0 γ) hciγ
          (fun x hx ↦ hanti.antitoneOn hx ⟨hγ0.le, le_rfl⟩ hx.2)
        simpa using hi
      have hprod := mul_pos (mul_pos hN hγ0) hpos
      nlinarith
    · have hneg_after : ∀ x ∈ Ioo γ (1 : ℝ), h x < 0 := by
        intro x hx
        have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hγ0.trans hx.1, hx.2⟩
        have hrγ : f γ / g γ ≤ 1 := (div_le_one (hgp γ hγmem)).mpr (by dsimp [h] at hpos; linarith)
        have hrx := hr hγmem hx' hx.1
        have : f x < g x := (div_lt_one (hgp x hx')).mp (hrx.trans_le hrγ)
        dsimp [h]
        linarith
      have hnegative : (∫ x in γ..(1 : ℝ), h x) < 0 := by
        have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
          (g := fun _ ↦ (0 : ℝ)) hγ1 (hc.mono hsub') continuousOn_const
          (fun x hx ↦ ?_) ?_
        · simpa using hi
        · by_cases hx1 : x = 1
          · simp [h, hx1, hone]
          · exact (hneg_after x ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩).le
        · refine ⟨(γ + 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
          exact hneg_after _ ⟨by linarith, by linarith⟩
      have hadd := intervalIntegral.integral_add_adjacent_intervals hciγ hciγ'
      rw [htotal] at hadd
      have hpositive : 0 < ∫ x in (0 : ℝ)..γ, h x := by linarith
      have hp := mul_pos (by linarith : 0 < N + 1) hpositive
      have hn := mul_nonpos_of_nonneg_of_nonpos hγ0.le (le_of_not_gt hpos)
      linarith
  rw [show h = fun x ↦ f x - g x from rfl, intervalIntegral.integral_sub hfiγ hgiγ] at hgoal
  dsimp at hgoal
  linarith

/-- Strict switch ordering on the left half of the index range (SWORDER). -/
theorem switchValue_strict_order {n i j : ℕ} (hi : 0 < i) (hij : i < j)
    (hj : j ≤ n / 2) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchValue n j γ < switchValue n i γ := by
  have hj0 : 0 < j := by omega
  have hjn : j < n := by omega
  have hin : i < n := by omega
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let A := fun x ↦ (n : ℝ) * switchRatio n i x / (x * (1 - switchRatio n i x))
  let B := fun x ↦ (n : ℝ) * switchRatio n j x / (x * (1 - switchRatio n j x))
  have hrate : ∀ x ∈ Ioo (0 : ℝ) 1, B x < A x := by
    intro x hx
    have hRi := switchRatio_bounds hi hin hx.1 hx.2
    have hRj := switchRatio_bounds hj0 hjn hx.1 hx.2
    have hR := switchRatio_strict_order hi hij hj hx.1 hx.2
    apply (div_lt_div_iff₀ (mul_pos hx.1 (sub_pos.mpr hRj.2))
      (mul_pos hx.1 (sub_pos.mpr hRi.2))).mpr
    have hp := mul_pos (mul_pos hn hx.1) (sub_pos.mpr hR)
    nlinarith
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (switchMass n i) (-A x * switchMass n i x) x := by
    intro x hx
    simpa [A, neg_div] using hasDerivAt_switchMass hi hin hx.1 hx.2
  have hg : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (switchMass n j) (-B x * switchMass n j x) x := by
    intro x hx
    simpa [B, neg_div] using hasDerivAt_switchMass hj0 hjn hx.1 hx.2
  have hcomp := integral_endpoint_strict_comparison hn hγ0 hγ1
    (continuousOn_switchMass hi hin) (continuousOn_switchMass hj0 hjn)
    hf hg (fun x hx ↦ switchMass_pos hi hin hx.1 hx.2)
    (fun x hx ↦ switchMass_pos hj0 hjn hx.1 hx.2)
    (fun x hx ↦ div_pos (mul_pos hn (switchRatio_bounds hj0 hjn hx.1 hx.2).1)
      (mul_pos hx.1 (sub_pos.mpr (switchRatio_bounds hj0 hjn hx.1 hx.2).2)))
    hrate (by simp [switchMass_one hin, switchMass_one hjn])
    (by rw [integral_switchMass hi hin, integral_switchMass hj0 hjn])
  simpa only [switchValue_eq_integral_mass hi hin hγ0.le hγ1.le,
    switchValue_eq_integral_mass hj0 hjn hγ0.le hγ1.le] using hcomp

/-- Every noncentral switch has strictly larger value than the central switch. -/
theorem switchValue_central_lt {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    (hjc : j ≠ n / 2) (hjrc : j ≠ n - n / 2)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchValue n (n / 2) γ < switchValue n j γ := by
  by_cases hjhalf : j ≤ n / 2
  · exact switchValue_strict_order hj (by omega) le_rfl hγ0 hγ1
  · rw [← switchValue_reflection hj hjn hγ0 hγ1]
    exact switchValue_strict_order (by omega : 0 < n - j)
      (by omega : n - j < n / 2) le_rfl hγ0 hγ1

/-- The central switch minimizes the value over all interior switch indices. -/
theorem switchValue_central_le {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchValue n (n / 2) γ ≤ switchValue n j γ := by
  by_cases hjc : j = n / 2
  · subst j
    exact le_rfl
  by_cases hjrc : j = n - n / 2
  · subst j
    rw [switchValue_reflection (by omega : 0 < n / 2) (by omega : n / 2 < n) hγ0 hγ1]
  exact (switchValue_central_lt hj hjn hjc hjrc hγ0 hγ1).le

/-- Exactly the central index and its reflection attain the minimum among switches. -/
theorem switchValue_eq_central_iff {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchValue n j γ = switchValue n (n / 2) γ ↔
      j = n / 2 ∨ j = n - n / 2 := by
  constructor
  · intro heq
    by_contra h
    push Not at h
    exact (switchValue_central_lt hj hjn h.1 h.2 hγ0 hγ1).ne heq.symm
  · rintro (rfl | rfl)
    · rfl
    · exact switchValue_reflection (by omega : 0 < n / 2) (by omega : n / 2 < n) hγ0 hγ1

end PoissonBinomialComparison
