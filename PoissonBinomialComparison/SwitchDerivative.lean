import PoissonBinomialComparison.SwitchFunctions
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Interior switch differentiation

The implicit function theorem is applied to the polynomial equal-height
equation. Its partial derivative in the lower parameter is nonzero because
the two parameters lie on opposite sides of the unique critical point.
-/

namespace PoissonBinomialComparison

open Filter
open scoped Topology

private theorem hasStrictDerivAt_height {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    (x : ℝ) :
    HasStrictDerivAt (fun u : ℝ ↦ u ^ j * (1 - u) ^ (n - j))
      (x ^ (j - 1) * (1 - x) ^ (n - j - 1) * ((j : ℝ) - n * x)) x := by
  have hd := ((hasStrictDerivAt_id x).pow j).mul
    (((hasStrictDerivAt_const x (1 : ℝ)).sub (hasStrictDerivAt_id x)).pow (n - j))
  convert hd using 1
  · funext u
    rfl
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
  have hjpow : x ^ j = x ^ (j - 1) * x := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  have hnjpow : (1 - x) ^ (n - j) = (1 - x) ^ (n - j - 1) * (1 - x) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n - j)]
  rw [hjpow, hnjpow, Nat.cast_sub hjn.le]
  ring

private theorem implicit_height_solution {g : ℝ → ℝ} {γ b da db : ℝ}
    (ha : HasStrictDerivAt g da (γ + b)) (hb : HasStrictDerivAt g db b)
    (hne : da - db ≠ 0) :
    ∃ ψ : ℝ → ℝ, DifferentiableAt ℝ ψ γ ∧ Tendsto ψ (𝓝 γ) (𝓝 b) ∧
      ∀ᶠ t in 𝓝 γ, g (t + ψ t) - g (ψ t) = g (γ + b) - g b := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    da • (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) -
      db • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hF : HasStrictFDerivAt (fun z : ℝ × ℝ ↦ g (z.1 + z.2) - g z.2) L (γ, b) := by
    exact (ha.comp_hasStrictFDerivAt (γ, b)
      (hasStrictFDerivAt_fst.add hasStrictFDerivAt_snd)).sub
      (hb.comp_hasStrictFDerivAt (γ, b) hasStrictFDerivAt_snd)
  have hL : L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      (da - db) • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [L]
  have hinv : (L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hL]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (da - db)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [hne]
    · ext
      simp [hne]
  refine ⟨hF.implicitFunctionOfProdDomain hinv,
    (hF.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.differentiableAt,
    hF.tendsto_implicitFunctionOfProdDomain hinv, ?_⟩
  exact hF.eventually_apply_implicitFunctionOfProdDomain hinv

/-- The lower switch parameter is differentiable throughout the interior gap range. -/
theorem differentiableAt_switchLower {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    DifferentiableAt ℝ (switchLower n j) γ := by
  let a := switchUpper n j γ
  let b := switchLower n j γ
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha0 : 0 < a := lt_trans hs.1 hs.2.1
  have ha1 : 0 < 1 - a := by linarith [hs.2.2.1]
  have hb1 : 0 < 1 - b := by linarith [hs.2.1, hs.2.2.1]
  have hda : a ^ (j - 1) * (1 - a) ^ (n - j - 1) * ((j : ℝ) - n * a) < 0 := by
    have hja : (j : ℝ) < a * n := (div_lt_iff₀ hn).mp hc.2
    exact mul_neg_of_pos_of_neg (mul_pos (pow_pos ha0 _) (pow_pos ha1 _)) (by nlinarith)
  have hdb : 0 < b ^ (j - 1) * (1 - b) ^ (n - j - 1) * ((j : ℝ) - n * b) := by
    have hjb : b * n < (j : ℝ) := (lt_div_iff₀ hn).mp hc.1
    exact mul_pos (mul_pos (pow_pos hs.1 _) (pow_pos hb1 _)) (by nlinarith)
  have hab : γ + b = a := by linarith [hs.2.2.2.1]
  obtain ⟨ψ, hψd, hψt, hψeq⟩ := implicit_height_solution (γ := γ) (b := b)
    (by rw [hab]; exact hasStrictDerivAt_height hj hjn a)
    (hasStrictDerivAt_height hj hjn b) (by linarith :
      a ^ (j - 1) * (1 - a) ^ (n - j - 1) * ((j : ℝ) - n * a) -
        b ^ (j - 1) * (1 - b) ^ (n - j - 1) * ((j : ℝ) - n * b) ≠ 0)
  have heq : (switchLower n j) =ᶠ[𝓝 γ] ψ := by
    have evb : ∀ᶠ t in 𝓝 γ, 0 < ψ t := hψt.eventually (Ioi_mem_nhds hs.1)
    have hva : γ + b < 1 := hab ▸ hs.2.2.1
    have eva : ∀ᶠ t in 𝓝 γ, t + ψ t < 1 :=
      (tendsto_id.add hψt).eventually (Iio_mem_nhds hva)
    filter_upwards [hψeq, evb, eva, Ioo_mem_nhds hγ0 hγ1] with t ht htb hta htγ
    have htS : IsSwitch n j t (t + ψ t) (ψ t) := by
      refine ⟨htb, by linarith [htγ.1], hta, by ring, ?_⟩
      rw [hab, hs.2.2.2.2, sub_self] at ht
      exact sub_eq_zero.mp ht
    exact (htS.eq_switchPair hj hjn).2.symm
  exact hψd.congr_of_eventuallyEq heq

/-- The upper switch parameter is differentiable throughout the interior gap range. -/
theorem differentiableAt_switchUpper {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    DifferentiableAt ℝ (switchUpper n j) γ := by
  have heq : switchUpper n j =ᶠ[𝓝 γ] (fun t ↦ t + switchLower n j t) := by
    filter_upwards [Ioo_mem_nhds hγ0 hγ1] with t ht
    have h := switchUpper_sub_switchLower hj hjn ht.1 ht.2
    linarith
  exact (differentiableAt_id.add (differentiableAt_switchLower hj hjn hγ0 hγ1)).congr_of_eventuallyEq heq

private theorem height_derivative_times {n j : ℕ} (hj : 0 < j) (hjn : j < n) (x : ℝ) :
    (x ^ (j - 1) * (1 - x) ^ (n - j - 1) * ((j : ℝ) - n * x)) * (x * (1 - x)) =
      (x ^ j * (1 - x) ^ (n - j)) * ((j : ℝ) - n * x) := by
  have hjpow : x ^ j = x ^ (j - 1) * x := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  have hnjpow : (1 - x) ^ (n - j) = (1 - x) ^ (n - j - 1) * (1 - x) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n - j)]
  rw [hjpow, hnjpow]
  ring

/-- Differentiating the prescribed gap gives the difference of endpoint derivatives. -/
theorem deriv_switchUpper_sub_lower {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (switchUpper n j) γ - deriv (switchLower n j) γ = 1 := by
  have hd := (differentiableAt_switchUpper hj hjn hγ0 hγ1).hasDerivAt.sub
    (differentiableAt_switchLower hj hjn hγ0 hγ1).hasDerivAt
  have heq : (fun t : ℝ ↦ t) =ᶠ[𝓝 γ] (switchUpper n j - switchLower n j) := by
    filter_upwards [Ioo_mem_nhds hγ0 hγ1] with t ht
    exact (switchUpper_sub_switchLower hj hjn ht.1 ht.2).symm
  exact (hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id γ)

private theorem deriv_height_equation {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let a := switchUpper n j γ
    let b := switchLower n j γ
    ((j : ℝ) - n * a) * (b * (1 - b)) * deriv (switchUpper n j) γ =
      ((j : ℝ) - n * b) * (a * (1 - a)) * deriv (switchLower n j) γ := by
  dsimp
  let a := switchUpper n j γ
  let b := switchLower n j γ
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hdA := (hasStrictDerivAt_height hj hjn a).hasDerivAt.comp γ
    (differentiableAt_switchUpper hj hjn hγ0 hγ1).hasDerivAt
  have hdB := (hasStrictDerivAt_height hj hjn b).hasDerivAt.comp γ
    (differentiableAt_switchLower hj hjn hγ0 hγ1).hasDerivAt
  have heq : (fun t ↦ (switchUpper n j t) ^ j * (1 - switchUpper n j t) ^ (n - j))
      =ᶠ[𝓝 γ] (fun t ↦ (switchLower n j t) ^ j * (1 - switchLower n j t) ^ (n - j)) := by
    filter_upwards [Ioo_mem_nhds hγ0 hγ1] with t ht
    exact (switchPair_spec hj hjn ht.1 ht.2).2.2.2.2
  have hdEq := hdA.unique (hdB.congr_of_eventuallyEq heq)
  have hm : a ^ j * (1 - a) ^ (n - j) ≠ 0 := by
    have ha0 : 0 < a := lt_trans hs.1 hs.2.1
    exact (mul_pos (pow_pos ha0 _) (pow_pos (by linarith [hs.2.2.1]) _)).ne'
  apply mul_left_cancel₀ hm
  calc
    _ = (a ^ (j - 1) * (1 - a) ^ (n - j - 1) * ((j : ℝ) - n * a)) *
        deriv (switchUpper n j) γ * (a * (1 - a)) * (b * (1 - b)) := by
      convert congrArg (fun z : ℝ ↦ z * deriv (switchUpper n j) γ * (b * (1 - b)))
        (height_derivative_times hj hjn a).symm using 1 <;> dsimp [a, b] <;> ring
    _ = (b ^ (j - 1) * (1 - b) ^ (n - j - 1) * ((j : ℝ) - n * b)) *
        deriv (switchLower n j) γ * (a * (1 - a)) * (b * (1 - b)) := by rw [hdEq]
    _ = _ := by
      rw [hs.2.2.2.2]
      convert congrArg (fun z : ℝ ↦ z * deriv (switchLower n j) γ * (a * (1 - a)))
        (height_derivative_times hj hjn b) using 1 <;> dsimp [a, b] <;> ring

/-- The geometric ratio `R` associated with the canonical switch. -/
noncomputable def switchRatio (n j : ℕ) (γ : ℝ) : ℝ :=
  let c := (j : ℝ) / n
  (switchUpper n j γ - c) * (c - switchLower n j γ) / (c * (1 - c))

/-- The canonical geometric ratio lies strictly between zero and one. -/
theorem switchRatio_bounds {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    0 < switchRatio n j γ ∧ switchRatio n j γ < 1 :=
  (switchPair_spec hj hjn hγ0 hγ1).geometric_ratio_bounds hj hjn

private theorem deriv_switch_equations {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let a := switchUpper n j γ
    let b := switchLower n j γ
    let c := (j : ℝ) / n
    (a - c) * (b * (1 - b)) * deriv (switchUpper n j) γ +
      (c - b) * (a * (1 - a)) * deriv (switchLower n j) γ = 0 := by
  dsimp
  have hh := deriv_height_equation hj hjn hγ0 hγ1
  dsimp at hh
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnc : (n : ℝ) * ((j : ℝ) / n) = j := mul_div_cancel₀ _ hn
  apply (mul_eq_zero.mp ?_).resolve_left hn
  linear_combination -hh -
    (switchLower n j γ * (1 - switchLower n j γ) * deriv (switchUpper n j) γ -
      switchUpper n j γ * (1 - switchUpper n j γ) * deriv (switchLower n j) γ) * hnc

/-- The derivative of the upper switch parameter, in the manuscript's notation. -/
theorem deriv_switchUpper {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let a := switchUpper n j γ
    let b := switchLower n j γ
    let c := (j : ℝ) / n
    deriv (switchUpper n j) γ =
      (c - b) * a * (1 - a) / (γ * (c * (1 - c)) * (1 - switchRatio n j γ)) := by
  dsimp
  let a := switchUpper n j γ
  let b := switchLower n j γ
  let c := (j : ℝ) / n
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have hv : 0 < c * (1 - c) :=
    mul_pos (lt_trans hs.1 hc.1) (by linarith [hc.2, hs.2.2.1])
  have hR : 0 < 1 - switchRatio n j γ := sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2
  have hden : γ * (c * (1 - c)) * (1 - switchRatio n j γ) ≠ 0 :=
    (mul_pos (mul_pos hγ0 hv) hR).ne'
  apply (eq_div_iff hden).2
  have hn := hs.normalized_denominator hj hjn
  change c * (1 - c) * (1 - switchRatio n j γ) =
    c * (1 - a) * (1 - b) + (1 - c) * a * b at hn
  have hdeq : γ * (c * (1 - c)) * (1 - switchRatio n j γ) =
      (a - c) * (b * (1 - b)) + (c - b) * (a * (1 - a)) := by
    rw [mul_assoc, hn, ← hs.2.2.2.1]
    ring
  change deriv (switchUpper n j) γ * (γ * (c * (1 - c)) * (1 - switchRatio n j γ)) =
    (c - b) * a * (1 - a)
  rw [hdeq]
  have heq := deriv_switch_equations hj hjn hγ0 hγ1
  have hgap := deriv_switchUpper_sub_lower hj hjn hγ0 hγ1
  change (a - c) * (b * (1 - b)) * deriv (switchUpper n j) γ +
    (c - b) * (a * (1 - a)) * deriv (switchLower n j) γ = 0 at heq
  linear_combination heq + ((c - b) * (a * (1 - a))) * hgap

/-- The derivative of the lower switch parameter, in the manuscript's notation. -/
theorem deriv_switchLower {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let a := switchUpper n j γ
    let b := switchLower n j γ
    let c := (j : ℝ) / n
    deriv (switchLower n j) γ =
      -(a - c) * b * (1 - b) / (γ * (c * (1 - c)) * (1 - switchRatio n j γ)) := by
  dsimp
  let a := switchUpper n j γ
  let b := switchLower n j γ
  let c := (j : ℝ) / n
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have hv : 0 < c * (1 - c) :=
    mul_pos (lt_trans hs.1 hc.1) (by linarith [hc.2, hs.2.2.1])
  have hR : 0 < 1 - switchRatio n j γ := sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2
  have hden : γ * (c * (1 - c)) * (1 - switchRatio n j γ) ≠ 0 :=
    (mul_pos (mul_pos hγ0 hv) hR).ne'
  apply (eq_div_iff hden).2
  have hn := hs.normalized_denominator hj hjn
  change c * (1 - c) * (1 - switchRatio n j γ) =
    c * (1 - a) * (1 - b) + (1 - c) * a * b at hn
  have hdeq : γ * (c * (1 - c)) * (1 - switchRatio n j γ) =
      (a - c) * (b * (1 - b)) + (c - b) * (a * (1 - a)) := by
    rw [mul_assoc, hn, ← hs.2.2.2.1]
    ring
  change deriv (switchLower n j) γ * (γ * (c * (1 - c)) * (1 - switchRatio n j γ)) =
    -(a - c) * b * (1 - b)
  rw [hdeq]
  have heq := deriv_switch_equations hj hjn hγ0 hγ1
  have hgap := deriv_switchUpper_sub_lower hj hjn hγ0 hγ1
  change (a - c) * (b * (1 - b)) * deriv (switchUpper n j) γ +
    (c - b) * (a * (1 - a)) * deriv (switchLower n j) γ = 0 at heq
  linear_combination heq - ((a - c) * (b * (1 - b))) * hgap

/-- The common switching mass is strictly positive at every interior gap. -/
theorem switchMass_pos {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) : 0 < switchMass n j γ := by
  have hs := switchPair_spec hj hjn hγ0 hγ1
  have ha0 : 0 < switchUpper n j γ := lt_trans hs.1 hs.2.1
  have ha1 : 0 < 1 - switchUpper n j γ := by linarith [hs.2.2.1]
  have hc : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos hjn.le
  simp only [switchMass, pbMass_const]
  exact mul_pos (mul_pos hc (pow_pos ha0 _)) (pow_pos ha1 _)

private theorem hasDerivAt_switchMass_raw {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let a := switchUpper n j γ
    HasDerivAt (switchMass n j)
      (switchMass n j γ * ((j : ℝ) - n * a) / (a * (1 - a)) * deriv (switchUpper n j) γ) γ := by
  let a := switchUpper n j γ
  have hs := switchPair_spec hj hjn hγ0 hγ1
  have ha0 : a ≠ 0 := (lt_trans hs.1 hs.2.1).ne'
  have ha1 : 1 - a ≠ 0 := (sub_pos.mpr hs.2.2.1).ne'
  have hd := ((hasStrictDerivAt_height hj hjn a).hasDerivAt.comp γ
    (differentiableAt_switchUpper hj hjn hγ0 hγ1).hasDerivAt).const_mul (n.choose j : ℝ)
  convert hd using 1
  · funext t
    simp [switchMass, pbMass_const, mul_assoc]
  · change switchMass n j γ * ((j : ℝ) - n * a) / (a * (1 - a)) * _ = _
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (mul_ne_zero ha0 ha1)).2
    have ht := height_derivative_times hj hjn a
    simp only [switchMass, pbMass_const]
    convert congrArg (fun z : ℝ ↦ (n.choose j : ℝ) * z * deriv (switchUpper n j) γ)
      ht.symm using 1 <;> dsimp [a] <;> ring

/-- The derivative of the common switching mass. -/
theorem hasDerivAt_switchMass {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    HasDerivAt (switchMass n j)
      (-(n : ℝ) * switchRatio n j γ / (γ * (1 - switchRatio n j γ)) * switchMass n j γ) γ := by
  have hd := hasDerivAt_switchMass_raw hj hjn hγ0 hγ1
  dsimp at hd
  convert hd using 1
  let a := switchUpper n j γ
  let b := switchLower n j γ
  let c := (j : ℝ) / n
  let v := c * (1 - c)
  let R := switchRatio n j γ
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have ha0 : a ≠ 0 := (lt_trans hs.1 hs.2.1).ne'
  have ha1 : 1 - a ≠ 0 := (sub_pos.mpr hs.2.2.1).ne'
  have hv : v ≠ 0 := (mul_pos (lt_trans hs.1 hc.1) (by linarith [hc.2, hs.2.2.1])).ne'
  have hR : 1 - R ≠ 0 := (sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2).ne'
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnc : (n : ℝ) * c = j := mul_div_cancel₀ _ hn
  have hRv : R * v = (a - c) * (c - b) := div_mul_cancel₀ _ hv
  rw [deriv_switchUpper hj hjn hγ0 hγ1]
  change -(n : ℝ) * R / (γ * (1 - R)) * switchMass n j γ =
    switchMass n j γ * ((j : ℝ) - n * a) / (a * (1 - a)) *
      ((c - b) * a * (1 - a) / (γ * v * (1 - R)))
  field_simp
  linear_combination - (switchMass n j γ * (n : ℝ)) * hRv +
    (switchMass n j γ * (c - b)) * hnc

/-- The manuscript's logarithmic derivative identity `f'/f`. -/
theorem deriv_switchMass_div {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (switchMass n j) γ / switchMass n j γ =
      -(n : ℝ) * switchRatio n j γ / (γ * (1 - switchRatio n j γ)) := by
  rw [(hasDerivAt_switchMass hj hjn hγ0 hγ1).deriv]
  exact mul_div_cancel_right₀ _ (switchMass_pos hj hjn hγ0 hγ1).ne'

private theorem tail_density_times {n j : ℕ} (hj : 0 < j) (hjn : j < n) (t : ℝ) :
    ((n : ℝ) * pbMass (fun _ : Fin (n - 1) ↦ t) (j - 1)) * t =
      (j : ℝ) * pbMass (fun _ : Fin n ↦ t) j := by
  have hcoeff : (n : ℝ) * ((n - 1).choose (j - 1) : ℝ) = (n.choose j : ℝ) * j := by
    have hn1 : 1 ≤ n := by omega
    have hj1 : 1 ≤ j := by omega
    have hh := Nat.add_one_mul_choose_eq (n - 1) (j - 1)
    rw [Nat.sub_add_cancel hn1, Nat.sub_add_cancel hj1] at hh
    exact_mod_cast hh
  have hexp : n - 1 - (j - 1) = n - j := by omega
  have hpow : t ^ j = t ^ (j - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  simp only [pbMass_const, hexp]
  rw [hpow]
  linear_combination (t ^ (j - 1) * (1 - t) ^ (n - j) * t) * hcoeff

private theorem hasDerivAt_tail_density_div {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ pbTail (fun _ : Fin n ↦ u) j)
      ((j : ℝ) * pbMass (fun _ : Fin n ↦ t) j / t) t := by
  have heq : (n : ℝ) * pbMass (fun _ : Fin (n - 1) ↦ t) (j - 1) =
      (j : ℝ) * pbMass (fun _ : Fin n ↦ t) j / t :=
    (eq_div_iff ht).2 (tail_density_times hj hjn t)
  rw [← heq]
  exact hasDerivAt_pbTail_const n j hj t

/-- The derivative of the homogeneous switching value, exactly `F' = nf/(1-R)`. -/
theorem hasDerivAt_switchValue {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    HasDerivAt (switchValue n j)
      ((n : ℝ) * switchMass n j γ / (1 - switchRatio n j γ)) γ := by
  let a := switchUpper n j γ
  let b := switchLower n j γ
  let c := (j : ℝ) / n
  let v := c * (1 - c)
  let R := switchRatio n j γ
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have ha0 : a ≠ 0 := (lt_trans hs.1 hs.2.1).ne'
  have hb0 : b ≠ 0 := hs.1.ne'
  have hv : v ≠ 0 := (mul_pos (lt_trans hs.1 hc.1) (by linarith [hc.2, hs.2.2.1])).ne'
  have hR : 1 - R ≠ 0 := (sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2).ne'
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnc : (n : ℝ) * c = j := mul_div_cancel₀ _ hn
  have hdA := (hasDerivAt_tail_density_div hj hjn ha0).comp γ
    (differentiableAt_switchUpper hj hjn hγ0 hγ1).hasDerivAt
  have hdB := (hasDerivAt_tail_density_div hj hjn hb0).comp γ
    (differentiableAt_switchLower hj hjn hγ0 hγ1).hasDerivAt
  convert hdA.sub hdB using 1
  · rfl
  · change (n : ℝ) * switchMass n j γ / (1 - R) =
      ((j : ℝ) * switchMass n j γ / a) * deriv (switchUpper n j) γ -
        ((j : ℝ) * pbMass (fun _ : Fin n ↦ b) j / b) * deriv (switchLower n j) γ
    rw [← switchMass_eq_lower hj hjn hγ0 hγ1, deriv_switchUpper hj hjn hγ0 hγ1,
      deriv_switchLower hj hjn hγ0 hγ1]
    change (n : ℝ) * switchMass n j γ / (1 - R) =
      ((j : ℝ) * switchMass n j γ / a) * ((c - b) * a * (1 - a) / (γ * v * (1 - R))) -
      ((j : ℝ) * switchMass n j γ / b) * (-(a - c) * b * (1 - b) / (γ * v * (1 - R)))
    field_simp
    dsimp [v]
    linear_combination (switchMass n j γ * (a - b) * (1 - c)) * hnc -
      ((n : ℝ) * switchMass n j γ * c * (1 - c)) * hs.2.2.2.1

/-- The derivative of `F`, as a rewriting theorem. -/
theorem deriv_switchValue {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (switchValue n j) γ = (n : ℝ) * switchMass n j γ / (1 - switchRatio n j γ) :=
  (hasDerivAt_switchValue hj hjn hγ0 hγ1).deriv

/-- The derivative relation used to integrate the normalized switch identity. -/
theorem deriv_switchValue_eq_mass_sub {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (switchValue n j) γ =
      (n : ℝ) * switchMass n j γ - γ * deriv (switchMass n j) γ := by
  rw [deriv_switchValue hj hjn hγ0 hγ1, (hasDerivAt_switchMass hj hjn hγ0 hγ1).deriv]
  have hR : 1 - switchRatio n j γ ≠ 0 :=
    (sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2).ne'
  field_simp
  ring

/-- The canonical common mass is continuous on the complete gap interval. -/
theorem continuousOn_switchMass {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousOn (switchMass n j) (Set.Icc 0 1) := by
  intro γ hγ
  by_cases h0 : γ = 0
  · subst γ
    exact (continuousAt_switchMass_zero hj hjn).continuousWithinAt
  by_cases h1 : γ = 1
  · subst γ
    exact (continuousAt_switchMass_one hj hjn).continuousWithinAt
  exact (hasDerivAt_switchMass hj hjn (lt_of_le_of_ne hγ.1 (Ne.symm h0))
    (lt_of_le_of_ne hγ.2 h1)).continuousAt.continuousWithinAt

/-- The canonical switching value is continuous on the complete gap interval. -/
theorem continuousOn_switchValue {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousOn (switchValue n j) (Set.Icc 0 1) := by
  intro γ hγ
  by_cases h0 : γ = 0
  · subst γ
    exact (continuousAt_switchValue_zero hj hjn).continuousWithinAt
  by_cases h1 : γ = 1
  · subst γ
    exact (continuousAt_switchValue_one hj hjn).continuousWithinAt
  exact (hasDerivAt_switchValue hj hjn (lt_of_le_of_ne hγ.1 (Ne.symm h0))
    (lt_of_le_of_ne hγ.2 h1)).continuousAt.continuousWithinAt

end PoissonBinomialComparison
