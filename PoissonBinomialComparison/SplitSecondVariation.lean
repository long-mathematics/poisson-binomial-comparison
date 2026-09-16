import PoissonBinomialComparison.OtherVectorValues
import PoissonBinomialComparison.Compactness
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Splitting a repeated smaller lower parameter

These identities isolate the strict negative splitting coefficient and the
nonzero transverse derivative used by the tie-preserving perturbation argument.
The proofs retain deterministic randomizing variables.
-/

namespace PoissonBinomialComparison

open Finset Filter
open scoped Topology

noncomputable section

variable {n : ℕ} {q : Fin n → ℝ}

/-- Equal free gradients at unequal parameter values make the two consecutive
randomized double-deletion masses equal to that common gradient. -/
theorem randomized_double_delete_masses_eq {w c : ℝ} (k : ℕ) {i j : Fin n}
    (hneq : q i ≠ q j) (hGi : randomizedGradient q w k i = c)
    (hGj : randomizedGradient q w k j = c) :
    randomizedMassIntOn q ((univ.erase i).erase j) w ((k : ℤ) - 1) = c ∧
      randomizedMassIntOn q ((univ.erase i).erase j) w k = c := by
  have hij : i ≠ j := fun heq ↦ hneq (congrArg q heq)
  have hC : randomizedMixedCoefficient q w k i j = 0 := by
    have hd := randomizedGradient_sub q hij w k
    rw [hGi, hGj, sub_self] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (sub_ne_zero.mpr hneq.symm)
  have hgrad := randomizedGradient_eq_double_delete q hij w k
  rw [hGi, hC, mul_zero, add_zero] at hgrad
  have hB : randomizedMassIntOn q ((univ.erase i).erase j) w k = c := by
    rw [randomizedMassIntOn_natCast]
    exact hgrad.symm
  change randomizedCoefficientOn q ((univ.erase i).erase j) w k = 0 at hC
  rw [randomizedCoefficientOn_eq_int, hB] at hC
  exact ⟨by linarith, hB⟩

/-- When a smaller value occurs twice and a larger value has the same positive
free gradient, splitting the two smaller coordinates has strictly negative
mixed coefficient. This is the strict second-variation sign in QSPLIT. -/
theorem randomizedMixedCoefficient_neg_of_repeated_smaller (hq : ValidParameters q)
    {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c)
    (k : ℕ) {i j l : Fin n} (hij : i ≠ j) (heq : q i = q j) (hlt : q i < q l)
    (hGi : randomizedGradient q w k i = c)
    (hGl : randomizedGradient q w k l = c) :
    randomizedMixedCoefficient q w k i j < 0 := by
  have hil : i ≠ l := fun hh ↦ hlt.ne (congrArg q hh)
  have hjl : j ≠ l := by intro hh; exact hlt.ne (heq.trans (congrArg q hh))
  let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
  have hj : j ∉ s := by simp [s]
  have hl : l ∉ s := by simp [s]
  have hsij : insert l s = (univ.erase i).erase j := by
    apply insert_erase
    simp [hil.symm, hjl.symm]
  have hsil : insert j s = (univ.erase i).erase l := by
    ext t
    by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l <;>
      simp_all [s]
  let f := randomizedMassIntOn q s w
  have hconv (t : Fin n) (ht : t ∉ s) (a : ℤ) :
      randomizedMassIntOn q (insert t s) w a = bernoulliConvolve f (q t) a := by
    exact randomizedMassIntOn_insert q ht w a
  obtain ⟨hA, hB⟩ := randomized_double_delete_masses_eq k hlt.ne hGi hGl
  rw [← hsil, hconv j hj] at hA hB
  have hApos : 0 < bernoulliConvolve f (q j) ((k : ℤ) - 1) := by rwa [hA]
  have hBpos : 0 < bernoulliConvolve f (q j) ((k : ℤ) - 1 + 1) := by
    simpa only [sub_add_cancel] using (hB ▸ hc : 0 < bernoulliConvolve f (q j) k)
  have hdet := bernoulliConvolve_strict_adjacent
    (randomizedMassIntOn_nonneg (fun t (_ : t ∈ s) ↦ hq t) hw0 hw1)
    (randomizedMassIntOn_cross s (fun t _ ↦ hq t) hw0 hw1)
    (randomizedMassIntOn_strictLogConcavity s (fun t _ ↦ hq t) hw0 hw1)
    (hq j).1 (hq j).2 (by linarith : q j < q l) ((k : ℤ) - 1) hApos hBpos
  change bernoulliConvolve f (q l) ((k : ℤ) - 1) *
    bernoulliConvolve f (q j) ((k : ℤ) - 1 + 1) <
      bernoulliConvolve f (q l) ((k : ℤ) - 1 + 1) *
        bernoulliConvolve f (q j) ((k : ℤ) - 1) at hdet
  simp only [sub_add_cancel, hA, hB] at hdet
  have hsign := (mul_lt_mul_iff_left₀ hc).mp hdet
  change randomizedCoefficientOn q ((univ.erase i).erase j) w k < 0
  rw [randomizedCoefficientOn_eq_int, ← hsij, hconv l hl, hconv l hl]
  exact sub_neg.mpr hsign

/-- The bare double-deletion second count difference cannot vanish at unequal
coordinates with a common positive free gradient. This is the nonzero
transverse coefficient needed to preserve an active tie. -/
theorem double_deleted_second_difference_ne_zero (hq : ValidParameters q)
    {w c : ℝ} (hc : 0 < c) (k : ℕ) {i j : Fin n}
    (hneq : q i ≠ q j) (hGi : randomizedGradient q w k i = c)
    (hGj : randomizedGradient q w k j = c) :
    pbMassIntOn q ((univ.erase i).erase j) ((k : ℤ) - 2) -
        2 * pbMassIntOn q ((univ.erase i).erase j) ((k : ℤ) - 1) +
          pbMassIntOn q ((univ.erase i).erase j) k ≠ 0 := by
  intro hzero
  let s := ((univ : Finset (Fin n)).erase i).erase j
  let X := pbMassIntOn q s ((k : ℤ) - 2)
  let Y := pbMassIntOn q s ((k : ℤ) - 1)
  let Z := pbMassIntOn q s k
  change X - 2 * Y + Z = 0 at hzero
  obtain ⟨hA, hB⟩ := randomized_double_delete_masses_eq k hneq hGi hGj
  change (1 - w) * Y + w * pbMassIntOn q s ((k : ℤ) - 1 - 1) = c at hA
  rw [show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 by omega] at hA
  change (1 - w) * Y + w * X = c at hA
  change (1 - w) * Z + w * Y = c at hB
  have hXY : X - Y = Y - Z := by linarith
  have hXZ : X = 2 * Y - Z := by linarith
  rw [hXZ] at hA
  have hYZ : Y = Z := by nlinarith [hA, hB]
  have hXY' : X = Y := by linarith
  have hY : Y = c := by rw [← hYZ] at hB; nlinarith [hB]
  have hpos : 0 < pbMassIntOn q s ((k : ℤ) - 1) := by change 0 < Y; rwa [hY]
  have hLC := pbMassIntOn_strictLogConcavity s (fun t _ ↦ hq t) ((k : ℤ) - 1) hpos
  rw [show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 by omega,
    show (k : ℤ) - 1 + 1 = (k : ℤ) by omega] at hLC
  change X * Z < Y ^ 2 at hLC
  rw [hXY', ← hYZ] at hLC
  nlinarith

/-- The mass-tie transfer coefficient is nonzero; its negative is the
first derivative of the upper-minus-lower mass tie along the unequal transfer. -/
theorem mass_tie_transfer_coefficient_ne_zero (hq : ValidParameters q)
    {w c : ℝ} (hc : 0 < c) (k : ℕ) {i j : Fin n}
    (hneq : q i ≠ q j) (hGi : randomizedGradient q w k i = c)
    (hGj : randomizedGradient q w k j = c) :
    -(q j - q i) *
      (pbMassIntOn q ((univ.erase i).erase j) ((k : ℤ) - 2) -
        2 * pbMassIntOn q ((univ.erase i).erase j) ((k : ℤ) - 1) +
          pbMassIntOn q ((univ.erase i).erase j) k) ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hneq.symm))
    (double_deleted_second_difference_ne_zero hq hc k hneq hGi hGj)

/-- A nonzero transverse derivative and zero tangential derivative produce a
tie-preserving curve tangent to the splitting direction. -/
theorem exists_tie_preserving_curve {G : ℝ × ℝ → ℝ} {b : ℝ} (hb : b ≠ 0)
    (hG : HasStrictFDerivAt G (b • ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0)) :
    ∃ s : ℝ → ℝ, s 0 = 0 ∧ HasDerivAt s 0 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), G (t, s t) = G (0, 0) := by
  let L := b • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hL : L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ = b • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [L]
  have hinv1 : (b • ContinuousLinearMap.id ℝ ℝ) ∘L (b⁻¹ • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [hb]
  have hinv2 : (b⁻¹ • ContinuousLinearMap.id ℝ ℝ) ∘L (b • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [hb]
  have hinv : (L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hL]
    exact ContinuousLinearMap.IsInvertible.of_inverse hinv1 hinv2
  let s := hG.implicitFunctionOfProdDomain hinv
  have hs0 : s 0 = 0 :=
    (hG.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
  have hs : HasDerivAt s 0 0 := by
    have hd := (hG.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.hasDerivAt
    have hzero : L ∘L ContinuousLinearMap.inl ℝ ℝ ℝ = 0 := by ext; simp [L]
    change HasDerivAt s ((-(L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).inverse ∘L
      (L ∘L ContinuousLinearMap.inl ℝ ℝ ℝ)) 1) 0 at hd
    simpa only [hzero, ContinuousLinearMap.comp_zero, neg_zero, zero_apply] using hd
  exact ⟨s, hs0, hs, hG.eventually_apply_implicitFunctionOfProdDomain hinv⟩

/-- A negative splitting coefficient remains a strict decrease along any
curve tangent to the split. Only the first derivative of the transverse curve
is needed: its displacement divided by the split parameter tends to zero. -/
theorem quadratic_decrease_along_tangent_curve {J A B : ℝ × ℝ → ℝ} {C : ℝ}
    (hC : C < 0) (hA : ContinuousAt A (0, 0)) (hB : ContinuousAt B (0, 0))
    (hJ : ∀ z, J z = J (0, 0) + C * z.1 ^ 2 + z.1 * z.2 * A z + z.2 ^ 2 * B z)
    {s : ℝ → ℝ} (hs0 : s 0 = 0) (hs : HasDerivAt s 0 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), J (t, s t) < J (0, 0) := by
  have ht : Tendsto (fun t : ℝ ↦ t) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hst : Tendsto s (𝓝[≠] 0) (𝓝 0) := by
    simpa only [hs0] using hs.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hratio : Tendsto (fun t ↦ s t / t) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa [hs0, smul_eq_mul, div_eq_mul_inv, mul_comm] using hs.tendsto_slope_zero
  have hAt := hA.tendsto.comp (ht.prodMk_nhds hst)
  have hBt := hB.tendsto.comp (ht.prodMk_nhds hst)
  have hlim : Tendsto (fun t ↦ C + (s t / t) * A (t, s t) + (s t / t)^2 * B (t, s t))
      (𝓝[≠] (0 : ℝ)) (𝓝 C) := by
    simpa using (tendsto_const_nhds.add (hratio.mul hAt)).add ((hratio.pow 2).mul hBt)
  have hneg := hlim.eventually (Iio_mem_nhds hC)
  filter_upwards [hneg, self_mem_nhdsWithin] with t hneg htne
  have ht0 : t ≠ 0 := htne
  have heq : J (t, s t) - J (0, 0) =
      t^2 * (C + (s t / t) * A (t, s t) + (s t / t)^2 * B (t, s t)) := by
    rw [hJ (t, s t)]
    dsimp
    field_simp
    ring
  have hlt := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ht0) hneg
  rw [← heq] at hlt
  linarith

/-- The analytic constrained second-variation step: a transverse mass tie can
be preserved exactly while a negative split coefficient decreases the test. -/
theorem exists_tie_preserving_decreasing_curve {G J A B : ℝ × ℝ → ℝ} {b C : ℝ}
    (hb : b ≠ 0) (hG : HasStrictFDerivAt G (b • ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0))
    (hC : C < 0) (hA : ContinuousAt A (0, 0)) (hB : ContinuousAt B (0, 0))
    (hJ : ∀ z, J z = J (0, 0) + C * z.1 ^ 2 + z.1 * z.2 * A z + z.2 ^ 2 * B z) :
    ∃ s : ℝ → ℝ, s 0 = 0 ∧ HasDerivAt s 0 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), G (t, s t) = G (0, 0)) ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℝ), J (t, s t) < J (0, 0) := by
  obtain ⟨s, hs0, hs, heq⟩ := exists_tie_preserving_curve hb hG
  exact ⟨s, hs0, hs, heq, quadratic_decrease_along_tangent_curve hC hA hB hJ hs0 hs⟩

end

end PoissonBinomialComparison
