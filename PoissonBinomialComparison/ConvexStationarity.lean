import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Separation for two active gradients

A convex set of feasible directional derivatives that misses the strictly
negative quadrant admits a nonnegative supporting convex combination. This is
the separation step behind the manuscript's randomized-threshold stationarity.
-/

namespace PoissonBinomialComparison

open Set Filter
open scoped Topology

/-- Two linearized objectives with no simultaneous strict descent have a
supporting convex combination. No closedness assumption on the direction set
is needed. -/
theorem exists_weight_of_no_simultaneous_descent {C : Set (ℝ × ℝ)}
    (hC : Convex ℝ C) (hzero : (0, 0) ∈ C)
    (hdesc : ∀ x ∈ C, 0 ≤ max x.1 x.2) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ ∀ x ∈ C, 0 ≤ w*x.1 + (1-w)*x.2 := by
  let S : Set (ℝ × ℝ) := Iic 0 ×ˢ Iic 0
  have hS : Convex ℝ S := (convex_Iic (0 : ℝ)).prod (convex_Iic (0 : ℝ))
  have hint : interior S = Iio 0 ×ˢ Iio 0 := by
    dsimp only [S]
    rw [interior_prod_eq, interior_Iic]
  have hdisj : Disjoint (interior S) C := by
    rw [Set.disjoint_left]
    intro x hx hxC
    rw [hint] at hx
    exact (max_lt hx.1 hx.2).not_ge (hdesc x hxC)
  have hne : (interior S).Nonempty := by
    rw [hint]
    exact ⟨(-1,-1), by norm_num⟩
  obtain ⟨f, r, hf, hneg, hpos⟩ := geometric_hahn_banach_of_nonempty_interior
    hS hC hdisj hne ⟨(0,0),hzero⟩
  have hr : r = 0 := by
    have ha := hneg (0,0) (by simp [S])
    have hb := hpos (0,0) hzero
    simp only [← Prod.zero_eq_mk, map_zero] at ha hb
    exact le_antisymm hb ha
  subst r
  have hform (x : ℝ × ℝ) : f x = x.1*f (1,0) + x.2*f (0,1) := by
    have hx : x = x.1 • (1,0) + x.2 • (0,1) := by ext <;> simp
    calc
      f x = f (x.1 • (1,0) + x.2 • (0,1)) := congrArg f hx
      _ = _ := by rw [map_add, map_smul, map_smul]; rfl
  have hA : 0 ≤ f (1,0) := by
    have h := hneg (-1,0) (by simp [S])
    rw [hform] at h
    linarith
  have hB : 0 ≤ f (0,1) := by
    have h := hneg (0,-1) (by simp [S])
    rw [hform] at h
    linarith
  have hsum : 0 < f (1,0) + f (0,1) := by
    by_contra h
    have ha : f (1,0) = 0 := by linarith
    have hb : f (0,1) = 0 := by linarith
    apply hf
    apply ContinuousLinearMap.ext
    intro x
    simp [hform x, ha, hb]
  refine ⟨f (1,0) / (f (1,0) + f (0,1)), div_nonneg hA hsum.le,
    (div_le_one hsum).mpr (by linarith), ?_⟩
  intro x hx
  have h := hpos x hx
  rw [hform] at h
  have heq : f (1,0) / (f (1,0)+f (0,1))*x.1 +
      (1-f (1,0)/(f (1,0)+f (0,1)))*x.2 =
      (x.1*f (1,0)+x.2*f (0,1))/(f (1,0)+f (0,1)) := by
    field_simp
    ring
  rw [heq]
  exact div_nonneg h hsum.le

/-- A negative derivative gives strict decrease for all sufficiently small
positive steps, without assuming a derivative away from the base point. -/
theorem eventually_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {x d : ℝ}
    (hf : HasDerivAt f d x) (hd : d < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x+t) < f x := by
  have h := hf.tendsto_slope_zero_right.eventually (eventually_lt_nhds hd)
  filter_upwards [h, self_mem_nhdsWithin] with t ht ht0
  change 0 < t at ht0
  simp only [smul_eq_mul] at ht
  have hsub : f (x+t)-f x < 0 := neg_of_mul_neg_right ht (inv_nonneg.mpr ht0.le)
  linarith

/-- A right-hand local minimum of the maximum of two differentiable functions
forbids strict negativity of both derivatives. -/
theorem max_derivatives_nonneg_of_eventually_le {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0)
    (hmin : ∀ᶠ t in 𝓝[>] (0 : ℝ), max (f 0) (g 0) ≤ max (f t) (g t)) :
    0 ≤ max a b := by
  by_contra h
  have hab := max_lt_iff.mp (lt_of_not_ge h)
  have hF := eventually_lt_of_hasDerivAt_neg hf hab.1
  have hG := eventually_lt_of_hasDerivAt_neg hg hab.2
  obtain ⟨t, ht, hft, hgt⟩ := (hmin.and (hF.and hG)).exists
  simp only [zero_add] at hft hgt
  exact (max_lt (hft.trans_le (le_max_left _ _))
    (hgt.trans_le (le_max_right _ _))).not_ge ht

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The two-gradient alternative on any convex family of feasible directions. -/
theorem exists_supporting_gradient {V : Set E} (hV : Convex ℝ V) (hzero : 0 ∈ V)
    (f g : E →L[ℝ] ℝ) (hdesc : ∀ v ∈ V, 0 ≤ max (f v) (g v)) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ ∀ v ∈ V, 0 ≤ w*f v + (1-w)*g v := by
  let L := f.prod g
  have hC : Convex ℝ (L '' V) := hV.linear_image L.toLinearMap
  have hz : (0,0) ∈ L '' V := ⟨0, hzero, by simp [L]⟩
  obtain ⟨w, hw0, hw1, hw⟩ := exists_weight_of_no_simultaneous_descent hC hz (by
    rintro x ⟨v,hv,rfl⟩
    exact hdesc v hv)
  exact ⟨w, hw0, hw1, fun v hv ↦ hw (L v) ⟨v,hv,rfl⟩⟩

/-- First-order necessary condition for a maximum of two smooth functions
on any family of feasible positive rays. -/
theorem max_directionalDerivatives_nonneg {f g : E → ℝ} {x v : E}
    {f' g' : E →L[ℝ] ℝ} {S : Set E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hmin : IsLocalMinOn (fun y ↦ max (f y) (g y)) S x)
    (hv : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • v ∈ S) :
    0 ≤ max (f' v) (g' v) := by
  have hpath : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hF := hf.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have hG := hg.comp_hasDerivAt_of_eq 0 hpath (by simp)
  apply max_derivatives_nonneg_of_eventually_le hF hG
  have ht : Tendsto (fun t : ℝ ↦ x+t • v) (𝓝[>] 0) (𝓝[S] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using (hpath.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds), hv⟩
  simpa using ht.eventually hmin

/-- Existence of the active-gradient convex combination at a constrained local
minimum. The tangent family may be specified by exact linear sign constraints. -/
theorem exists_supporting_gradient_of_localMinOn {f g : E → ℝ} {x : E}
    {f' g' : E →L[ℝ] ℝ} {S V : Set E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hmin : IsLocalMinOn (fun y ↦ max (f y) (g y)) S x)
    (hV : Convex ℝ V) (hzero : 0 ∈ V)
    (hfeas : ∀ v ∈ V, ∀ᶠ t in 𝓝[>] (0 : ℝ), x+t • v ∈ S) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ ∀ v ∈ V, 0 ≤ w*f' v + (1-w)*g' v :=
  exists_supporting_gradient hV hzero f' g'
    (fun v hv ↦ max_directionalDerivatives_nonneg hf hg hmin (hfeas v hv))

end PoissonBinomialComparison
