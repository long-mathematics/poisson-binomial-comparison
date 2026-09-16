import PoissonBinomialComparison.SwitchMonotonicity
import PoissonBinomialComparison.BinomialAtom
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Strict concavity and the initial slope of the benchmark

The geometric bound on `R'` makes every switch value strictly concave in dimensions
at least three. Endpoint derivatives are right derivatives: the canonical switch
functions are clamped outside the manuscript's gap interval.
-/

namespace PoissonBinomialComparison

open Set Filter
open scoped Topology

/-- The second derivative expressed using the common mass and geometric ratio. -/
theorem hasDerivAt_deriv_switchValue {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    HasDerivAt (deriv (switchValue n j))
      ((n : ℝ) * (deriv (switchMass n j) γ * (1 - switchRatio n j γ) +
        switchMass n j γ * deriv (switchRatio n j) γ) / (1 - switchRatio n j γ)^2) γ := by
  have hf := (hasDerivAt_switchMass hj hjn hγ0 hγ1).differentiableAt.hasDerivAt
  have hR := (hasDerivAt_switchRatio_gap hj hjn hγ0 hγ1).differentiableAt.hasDerivAt
  have hd := (hf.const_mul (n : ℝ)).div ((hasDerivAt_const γ 1).sub hR)
    (sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2).ne'
  have heq : deriv (switchValue n j) =ᶠ[𝓝 γ]
      (fun x => (n : ℝ) * switchMass n j x / (1 - switchRatio n j x)) := by
    filter_upwards [Ioo_mem_nhds hγ0 hγ1] with x hx
    exact deriv_switchValue hj hjn hx.1 hx.2
  convert hd.congr_of_eventuallyEq heq using 1
  simp only [Pi.sub_apply]
  ring

/-- Every nontrivial switch has strictly negative second derivative for `n ≥ 3`. -/
theorem deriv2_switchValue_neg {n j : ℕ} (hn : 3 ≤ n) (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (deriv (switchValue n j)) γ < 0 := by
  rw [(hasDerivAt_deriv_switchValue hj hjn hγ0 hγ1).deriv]
  have hf := switchMass_pos hj hjn hγ0 hγ1
  obtain ⟨hR0,hR1⟩ := switchRatio_bounds hj hjn hγ0 hγ1
  have hRp := deriv_switchRatio_le hj hjn hγ0 hγ1
  have hnR : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have hf' : deriv (switchMass n j) γ * (1 - switchRatio n j γ) =
      -(n : ℝ) * switchRatio n j γ / γ * switchMass n j γ := by
    rw [(hasDerivAt_switchMass hj hjn hγ0 hγ1).deriv]
    field_simp [(sub_pos.mpr hR1).ne']
  rw [hf']
  apply div_neg_of_neg_of_pos
  · apply mul_neg_of_pos_of_neg (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hRp hf.le
    have hstrict : 0 < ((n : ℝ) - 2) * (switchRatio n j γ / γ) * switchMass n j γ :=
      mul_pos (mul_pos (sub_pos.mpr hnR) (div_pos hR0 hγ0)) hf
    simp only [div_eq_mul_inv] at *
    nlinarith
  · positivity

/-- Strict concavity holds on the full closed gap interval, including its endpoints. -/
theorem strictConcaveOn_switchValue {n j : ℕ} (hn : 3 ≤ n) (hj : 0 < j) (hjn : j < n) :
    StrictConcaveOn ℝ (Icc 0 1) (switchValue n j) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) (continuousOn_switchValue hj hjn)
  intro x hx
  rw [interior_Icc] at hx
  exact deriv2_switchValue_neg hn hj hjn hx.1 hx.2

/-- The geometric ratio tends to zero when the two switch endpoints coalesce. -/
theorem continuousAt_switchRatio_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchRatio n j) 0 := by
  unfold switchRatio
  exact (((continuousAt_switchUpper_zero hj hjn).sub continuousAt_const).mul
    (continuousAt_const.sub (continuousAt_switchLower_zero hj hjn))).div_const _

@[simp] theorem switchRatio_zero (n j : ℕ) : switchRatio n j 0 = 0 := by
  simp [switchRatio]

/-- The interior derivatives have the stated finite limit at the zero gap. -/
theorem tendsto_deriv_switchValue_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    Tendsto (deriv (switchValue n j)) (𝓝[>] 0)
      (𝓝 ((n : ℝ) * switchMass n j 0)) := by
  have hc := ((continuousAt_switchMass_zero hj hjn).const_mul (n : ℝ)).div
    ((continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 0).sub
      (continuousAt_switchRatio_zero hj hjn)) (by simp)
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [Pi.div_apply, Pi.sub_apply, switchRatio_zero, sub_zero, div_one] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
  exact (deriv_switchValue hj hjn hx.1 hx.2).symm

/-- The exact right derivative at the zero gap, with no regularity hypothesis. -/
theorem hasDerivWithinAt_switchValue_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    HasDerivWithinAt (switchValue n j) ((n : ℝ) * switchMass n j 0) (Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo 0 1)
  · intro x hx
    exact (hasDerivAt_switchValue hj hjn hx.1 hx.2).differentiableAt.differentiableWithinAt
  · exact (continuousAt_switchValue_zero hj hjn).continuousWithinAt
  · exact Ioo_mem_nhdsGT (by norm_num)
  · exact tendsto_deriv_switchValue_zero hj hjn

/-- All switch values increase strictly from zero to one. -/
theorem strictMonoOn_switchValue {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    StrictMonoOn (switchValue n j) (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) (continuousOn_switchValue hj hjn)
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_switchValue hj hjn hx.1 hx.2]
  exact div_pos (mul_pos (by exact_mod_cast (lt_trans hj hjn))
    (switchMass_pos hj hjn hx.1 hx.2))
    (sub_pos.mpr (switchRatio_bounds hj hjn hx.1 hx.2).2)

/-- The positive switch value is strictly below both its initial tangent and one. -/
theorem switchValue_strict_bounds {n j : ℕ} (hn : 3 ≤ n) (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    0 < switchValue n j γ ∧
      switchValue n j γ < min ((n : ℝ) * switchMass n j 0 * γ) 1 := by
  have hm := strictMonoOn_switchValue hj hjn
  have h0 := hm (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ⟨hγ0.le,hγ1.le⟩ hγ0
  have h1 := hm ⟨hγ0.le,hγ1.le⟩ (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hγ1
  simp only [switchValue_zero] at h0
  rw [switchValue_one hj hjn.le] at h1
  refine ⟨h0, lt_min ?_ h1⟩
  have hs := (strictConcaveOn_switchValue hn hj hjn).slope_lt_of_hasDerivWithinAt
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ⟨hγ0.le,hγ1.le⟩ hγ0
    ((hasDerivWithinAt_switchValue_zero hj hjn).mono Icc_subset_Ici_self)
  simp only [slope_def_field, switchValue_zero, sub_zero] at hs
  exact (div_lt_iff₀ hγ0).mp hs

/-- On the manuscript domain the endpoint conventions agree with the central switch. -/
theorem benchmark_eq_switchValue_of_mem {n : ℕ} (hn : 2 ≤ n) {Δ : ℝ}
    (hΔ : Δ ∈ Icc (0 : ℝ) n) :
    benchmark n Δ = switchValue n (n / 2) (Δ / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  by_cases h0 : Δ = 0
  · simp [h0]
  by_cases h1 : Δ = n
  · simp [h1, hn0, benchmark_at_dimension (by omega : 0 < n),
      switchValue_one (by omega : 0 < n / 2) (Nat.div_le_self n 2)]
  exact benchmark_eq_switchValue (lt_of_le_of_ne hΔ.1 (Ne.symm h0))
    (lt_of_le_of_ne hΔ.2 h1)

/-- The central common mass at zero is exactly the manuscript constant. -/
theorem switchMass_central_zero (n : ℕ) : switchMass n (n / 2) 0 = kappa n := by
  rw [switchMass_zero]
  rfl

/-- The benchmark is continuous on its entire natural domain. -/
theorem continuousOn_benchmark {n : ℕ} (hn : 2 ≤ n) :
    ContinuousOn (benchmark n) (Icc (0 : ℝ) n) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hc := (continuousOn_switchValue (by omega : 0 < n / 2)
    (by omega : n / 2 < n)).comp (continuous_id.div_const (n : ℝ)).continuousOn
    (show MapsTo (fun x : ℝ => x / n) (Icc 0 n) (Icc 0 1) from
      fun x hx => ⟨div_nonneg hx.1 hn0.le, (div_le_one hn0).mpr hx.2⟩)
  exact hc.congr (fun x hx => benchmark_eq_switchValue_of_mem hn hx)

/-- The benchmark is strictly concave, including at the endpoints of its domain. -/
theorem strictConcaveOn_benchmark {n : ℕ} (hn : 3 ≤ n) :
    StrictConcaveOn ℝ (Icc (0 : ℝ) n) (benchmark n) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hs := strictConcaveOn_switchValue hn (by omega : 0 < n / 2) (by omega : n / 2 < n)
  refine ⟨convex_Icc (0 : ℝ) n, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx' : x / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hx.1 hn0.le, (div_le_one hn0).mpr hx.2⟩
  have hy' : y / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hy.1 hn0.le, (div_le_one hn0).mpr hy.2⟩
  have hxy' : x / (n : ℝ) ≠ y / n := fun he => hxy ((div_left_inj' hn0.ne').mp he)
  have h := hs.2 hx' hy' hxy' ha hb hab
  rw [benchmark_eq_switchValue_of_mem (by omega) hx,
    benchmark_eq_switchValue_of_mem (by omega) hy,
    benchmark_eq_switchValue_of_mem (by omega)
      ((convex_Icc (0 : ℝ) n) hx hy ha.le hb.le hab)]
  simpa only [smul_eq_mul, add_div, mul_div_assoc] using h

/-- The exact initial slope of the benchmark, as a derivative within its domain. -/
theorem hasDerivWithinAt_benchmark_zero {n : ℕ} (hn : 2 ≤ n) :
    HasDerivWithinAt (benchmark n) (kappa n) (Icc (0 : ℝ) n) 0 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hd := (hasDerivWithinAt_switchValue_zero (by omega : 0 < n / 2)
    (by omega : n / 2 < n)).comp_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).div_const (n : ℝ)).hasDerivWithinAt
    (show MapsTo (fun x : ℝ => x / n) (Icc 0 n) (Ici 0) from
      fun x hx => div_nonneg hx.1 hn0.le) (by simp)
  have he : ((n : ℝ) * switchMass n (n / 2) 0) * (1 / n) = kappa n := by
    rw [switchMass_central_zero]
    field_simp
  rw [he] at hd
  exact hd.congr (fun x hx => benchmark_eq_switchValue_of_mem hn hx) (by simp)

/-- The initial slope is also the usual right derivative on the positive half-line. -/
theorem hasDerivWithinAt_benchmark_zero_right {n : ℕ} (hn : 2 ≤ n) :
    HasDerivWithinAt (benchmark n) (kappa n) (Ici 0) 0 := by
  apply (hasDerivWithinAt_benchmark_zero hn).mono_of_mem_nhdsWithin
  exact Icc_mem_nhdsGE (by positivity)

/-- The manuscript's strict linear and unit upper bounds for the benchmark. -/
theorem benchmark_strict_bounds {n : ℕ} (hn : 3 ≤ n) {Δ : ℝ}
    (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    0 < benchmark n Δ ∧ benchmark n Δ < min (kappa n * Δ) 1 := by
  have hn0 : (0 : ℝ) < n := by positivity
  rw [benchmark_eq_switchValue hΔ0 hΔn]
  have h := switchValue_strict_bounds hn (by omega : 0 < n / 2)
    (by omega : n / 2 < n) (div_pos hΔ0 hn0) ((div_lt_one hn0).mpr hΔn)
  rw [switchMass_central_zero] at h
  have he : (n : ℝ) * kappa n * (Δ / n) = kappa n * Δ := by field_simp
  rwa [he] at h

end PoissonBinomialComparison
