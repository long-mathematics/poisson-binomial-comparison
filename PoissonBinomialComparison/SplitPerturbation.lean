import PoissonBinomialComparison.SplitSecondVariation
import PoissonBinomialComparison.TailStationarity

/-!
# The feasible split-and-transfer perturbation

A split of two equal coordinates is combined with an unequal-coordinate
transfer. The exact triaffine finite-law formulas supply the polynomial data
for the tie-preserving second-variation argument.
-/

namespace PoissonBinomialComparison

open Finset Filter
open scoped Topology

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Inserting one parameter makes the mixed coefficient affine. -/
theorem randomizedCoefficientOn_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (w : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    randomizedCoefficientOn p (insert i s) w k = randomizedCoefficientOn p s w k +
      p i * (randomizedCoefficientOn p s w (k - 1) - randomizedCoefficientOn p s w k) := by
  unfold randomizedCoefficientOn
  simp only [show k ≠ 0 by omega, ite_false]
  rw [randomizedSlopeOn_insert p hi, randomizedSlopeOn_insert p hi]
  unfold randomizedCoefficientOn
  simp only [show k ≠ 0 by omega, ite_false]
  ring

/-- The randomized test is a symmetric triaffine polynomial in three coordinates. -/
theorem randomizedTailOn_insert_three (p : ι → ℝ) {s : Finset ι} {i j l : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hl : l ∉ s)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (w : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    randomizedTailOn p (insert i (insert j (insert l s))) w k =
      randomizedTailOn p s w k + (p i + p j + p l) * randomizedSlopeOn p s w k +
      (p i * p j + p i * p l + p j * p l) * randomizedCoefficientOn p s w k +
      p i * p j * p l *
        (randomizedCoefficientOn p s w (k - 1) - randomizedCoefficientOn p s w k) := by
  rw [randomizedTailOn_insert_insert p (by simp [hi, hil]) (by simp [hj, hjl]) hij,
    randomizedTailOn_insert p hl, randomizedSlopeOn_insert p hl,
    randomizedCoefficientOn_insert p hl w hk]
  ring

/-- The count mass is a symmetric triaffine polynomial in three coordinates. -/
theorem pbMassIntOn_insert_three (p : ι → ℝ) {s : Finset ι} {i j l : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hl : l ∉ s)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (k : ℤ) :
    pbMassIntOn p (insert i (insert j (insert l s))) k =
      pbMassIntOn p s k + (p i + p j + p l) *
        (pbMassIntOn p s (k - 1) - pbMassIntOn p s k) +
      (p i * p j + p i * p l + p j * p l) *
        (pbMassIntOn p s (k - 2) - 2 * pbMassIntOn p s (k - 1) + pbMassIntOn p s k) +
      p i * p j * p l *
        (pbMassIntOn p s (k - 3) - 3 * pbMassIntOn p s (k - 2) +
          3 * pbMassIntOn p s (k - 1) - pbMassIntOn p s k) := by
  simp only [pbMassIntOn_insert p (by simp [hi, hij, hil] : i ∉ insert j (insert l s)),
    pbMassIntOn_insert p (by simp [hj, hjl] : j ∉ insert l s), pbMassIntOn_insert p hl]
  rw [show k - 1 - 1 = k - 2 by omega, show k - 2 - 1 = k - 3 by omega]
  ring

variable {n : ℕ}

/-- The two-variable feasible direction: split `i,j` and transfer from `l` to `i`. -/
def splitTransfer (q : Fin n → ℝ) (i j l : Fin n) (z : ℝ × ℝ) : Fin n → ℝ :=
  Function.update (Function.update (Function.update q i (q i + z.1 + z.2)) j (q j - z.1)) l (q l - z.2)

@[simp] theorem splitTransfer_zero (q : Fin n → ℝ) (i j l : Fin n) :
    splitTransfer q i j l (0, 0) = q := by simp [splitTransfer]

@[fun_prop] theorem continuous_splitTransfer (q : Fin n → ℝ) (i j l : Fin n) :
    Continuous (splitTransfer q i j l) := by unfold splitTransfer; fun_prop

private theorem splitTransfer_congr (q : Fin n → ℝ) {i j l : Fin n} (z : ℝ × ℝ)
    {s : Finset (Fin n)} (hi : i ∉ s) (hj : j ∉ s) (hl : l ∉ s) :
    ∀ t ∈ s, splitTransfer q i j l z t = q t := by
  intro t ht
  have hti : t ≠ i := fun hh ↦ hi (hh ▸ ht)
  have htj : t ≠ j := fun hh ↦ hj (hh ▸ ht)
  have htl : t ≠ l := fun hh ↦ hl (hh ▸ ht)
  simp [splitTransfer, Function.update_of_ne hti, Function.update_of_ne htj, Function.update_of_ne htl]

private theorem randomizedTailOn_congr' {p q : Fin n → ℝ} {s : Finset (Fin n)}
    (h : ∀ t ∈ s, p t = q t) (w : ℝ) (k : ℕ) :
    randomizedTailOn p s w k = randomizedTailOn q s w k := by
  simp only [randomizedTailOn, pbTailOn_congr h]

private theorem randomizedSlopeOn_congr' {p q : Fin n → ℝ} {s : Finset (Fin n)}
    (h : ∀ t ∈ s, p t = q t) (w : ℝ) (k : ℕ) :
    randomizedSlopeOn p s w k = randomizedSlopeOn q s w k := by
  simp only [randomizedSlopeOn, pbMassOn_congr h]

private theorem randomizedCoefficientOn_congr' {p q : Fin n → ℝ} {s : Finset (Fin n)}
    (h : ∀ t ∈ s, p t = q t) (w : ℝ) (k : ℕ) :
    randomizedCoefficientOn p s w k = randomizedCoefficientOn q s w k := by
  simp only [randomizedCoefficientOn, randomizedSlopeOn_congr' h]

/-- Exact mean preservation of the split-and-transfer perturbation. -/
theorem sum_splitTransfer (q : Fin n → ℝ) {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (z : ℝ × ℝ) :
    ∑ t, splitTransfer q i j l z t = ∑ t, q t := by
  have hsum (f : Fin n → ℝ) (t : Fin n) (a : ℝ) :
      ∑ x, Function.update f t a x = a + ∑ x, f x - f t := by
    rw [sum_update_of_mem (mem_univ _), sdiff_singleton_eq_erase,
      sum_erase_eq_sub (mem_univ _)]
    ring
  simp only [splitTransfer, hsum, Function.update_of_ne hil.symm,
    Function.update_of_ne hjl.symm, Function.update_of_ne hij.symm]
  ring

/-- Exact randomized-objective polynomial along the split-and-transfer plane.
The free-gradient equality removes its linear terms and its pure transfer term. -/
theorem randomizedTail_splitTransfer (q : Fin n → ℝ) {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (heq : q i = q j)
    {w c : ℝ} {k : ℕ} (hk : 1 ≤ k) (hneq : q i ≠ q l)
    (hGi : randomizedGradient q w k i = c) (hGl : randomizedGradient q w k l = c)
    (z : ℝ × ℝ) :
    let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
    let D := randomizedCoefficientOn q s w (k - 1) - randomizedCoefficientOn q s w k
    randomizedTail (splitTransfer q i j l z) w k - randomizedTail q w k =
      -randomizedMixedCoefficient q w k i j * z.1^2 -
        z.1*z.2*(randomizedMixedCoefficient q w k i j - D*z.1 - D*z.2) := by
  dsimp only
  let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
  let D := randomizedCoefficientOn q s w (k - 1) - randomizedCoefficientOn q s w k
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hl : l ∉ s := by simp [s]
  have hsij : insert l s = (univ.erase i).erase j := by
    apply insert_erase
    simp [hil.symm, hjl.symm]
  have hsil : insert j s = (univ.erase i).erase l := by
    ext t
    by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l <;>
      simp_all [s]
  have hfull : insert i (insert j (insert l s)) = univ := by
    rw [hsij, insert_erase (by simp [hij.symm]), insert_erase (mem_univ i)]
  have hCil : randomizedMixedCoefficient q w k i l = 0 := by
    have hd := randomizedGradient_sub q hil w k
    rw [hGi, hGl, sub_self] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (sub_ne_zero.mpr hneq.symm)
  change randomizedCoefficientOn q ((univ.erase i).erase l) w k = 0 at hCil
  rw [← hsil, randomizedCoefficientOn_insert q hj w hk, ← heq] at hCil
  have hbase : randomizedCoefficientOn q s w k = -q i * D := by
    change randomizedCoefficientOn q s w k + q i * D = 0 at hCil
    linarith
  have hCij : randomizedMixedCoefficient q w k i j = randomizedCoefficientOn q s w k + q l * D := by
    change randomizedCoefficientOn q ((univ.erase i).erase j) w k = _
    rw [← hsij, randomizedCoefficientOn_insert q hl w hk]
  have hold := randomizedTailOn_insert_three q hi hj hl hij hil hjl w hk
  have hnew := randomizedTailOn_insert_three (splitTransfer q i j l z) hi hj hl hij hil hjl w hk
  have hcongr := splitTransfer_congr q z hi hj hl
  rw [hfull] at hold hnew
  simp only [randomizedTailOn_congr' hcongr, randomizedSlopeOn_congr' hcongr,
    randomizedCoefficientOn_congr' hcongr] at hnew
  simp only [splitTransfer, Function.update_of_ne hil, Function.update_of_ne hij,
    Function.update_of_ne hjl, Function.update_self] at hnew
  change randomizedTail (splitTransfer q i j l z) w k = _ at hnew
  change randomizedTail q w k = _ at hold
  rw [hnew, hold, hCij]
  change _ = -(randomizedCoefficientOn q s w k + q l * D) * z.1^2 -
    z.1*z.2*(randomizedCoefficientOn q s w k + q l * D - D*z.1 - D*z.2)
  change _ + _ + _ + _ * D - (_ + _ + _ + _ * D) = _
  rw [hbase, ← heq]
  ring

/-- Exact count-mass polynomial along the split-and-transfer plane. -/
theorem pbMass_splitTransfer (q : Fin n → ℝ) {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (heq : q i = q j)
    (k : ℕ) (z : ℝ × ℝ) :
    let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
    let C := pbMassIntOn q s ((k : ℤ) - 2) - 2 * pbMassIntOn q s ((k : ℤ) - 1) + pbMassIntOn q s k
    let D := pbMassIntOn q s ((k : ℤ) - 3) - 3 * pbMassIntOn q s ((k : ℤ) - 2) +
      3 * pbMassIntOn q s ((k : ℤ) - 1) - pbMassIntOn q s k
    pbMass (splitTransfer q i j l z) k - pbMass q k =
      (q l - q i) * (C + q i * D) * z.2 - (C + q l * D) * z.1^2 -
      (C + q l * D) * z.1*z.2 - (C + q i * D) * z.2^2 + D*z.1^2*z.2 + D*z.1*z.2^2 := by
  dsimp only
  let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hl : l ∉ s := by simp [s]
  have hsij : insert l s = (univ.erase i).erase j := by
    apply insert_erase
    simp [hil.symm, hjl.symm]
  have hfull : insert i (insert j (insert l s)) = univ := by
    rw [hsij, insert_erase (by simp [hij.symm]), insert_erase (mem_univ i)]
  have hold := pbMassIntOn_insert_three q hi hj hl hij hil hjl (k : ℤ)
  have hnew := pbMassIntOn_insert_three (splitTransfer q i j l z) hi hj hl hij hil hjl (k : ℤ)
  have hcongr := splitTransfer_congr q z hi hj hl
  rw [hfull, pbMassIntOn_natCast] at hold hnew
  simp only [pbMassIntOn_congr hcongr] at hnew
  simp only [splitTransfer, Function.update_of_ne hil, Function.update_of_ne hij,
    Function.update_of_ne hjl, Function.update_self] at hnew
  change pbMass (splitTransfer q i j l z) k = _ at hnew
  change pbMass q k = _ at hold
  rw [hnew, hold, ← heq]
  ring

/-- The mass has zero derivative in the equal-coordinate split direction;
its transverse derivative is the unequal-coordinate second-count coefficient. -/
theorem hasStrictFDerivAt_pbMass_splitTransfer (q : Fin n → ℝ) {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (heq : q i = q j) (k : ℕ) :
    HasStrictFDerivAt (fun z ↦ pbMass (splitTransfer q i j l z) k)
      (((q l - q i) *
        (pbMassIntOn q ((univ.erase i).erase l) ((k : ℤ) - 2) -
          2 * pbMassIntOn q ((univ.erase i).erase l) ((k : ℤ) - 1) +
            pbMassIntOn q ((univ.erase i).erase l) k)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := by
  let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
  let C := pbMassIntOn q s ((k : ℤ) - 2) - 2 * pbMassIntOn q s ((k : ℤ) - 1) + pbMassIntOn q s k
  let D := pbMassIntOn q s ((k : ℤ) - 3) - 3 * pbMassIntOn q s ((k : ℤ) - 2) +
      3 * pbMassIntOn q s ((k : ℤ) - 1) - pbMassIntOn q s k
  have hj : j ∉ s := by simp [s]
  have hsil : insert j s = (univ.erase i).erase l := by
    ext t
    by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l <;>
      simp_all [s]
  have hcoef : pbMassIntOn q ((univ.erase i).erase l) ((k : ℤ) - 2) -
      2 * pbMassIntOn q ((univ.erase i).erase l) ((k : ℤ) - 1) +
        pbMassIntOn q ((univ.erase i).erase l) k = C + q i * D := by
    rw [← hsil]
    simp only [pbMassIntOn_insert q hj]
    dsimp [C, D]
    rw [show (k : ℤ) - 2 - 1 = (k : ℤ) - 3 by omega,
      show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 by omega, ← heq]
    ring
  rw [hcoef]
  have ht : HasStrictFDerivAt (fun z : ℝ × ℝ ↦ z.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 0) := hasStrictFDerivAt_fst
  have hs : HasStrictFDerivAt (fun z : ℝ × ℝ ↦ z.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := hasStrictFDerivAt_snd
  have hpoly := ((((((hasStrictFDerivAt_const (pbMass q k) (0, 0)).add
    (hs.const_mul ((q l - q i) * (C + q i * D)))).sub
    ((ht.mul ht).const_mul (C + q l * D))).sub
    ((ht.mul hs).const_mul (C + q l * D))).sub
    ((hs.mul hs).const_mul (C + q i * D))).add
    (((ht.mul ht).mul hs).const_mul D)).add (((ht.mul hs).mul hs).const_mul D)
  simp only [Pi.mul_apply, mul_zero, zero_smul,
    smul_zero, zero_add, add_zero, sub_zero] at hpoly
  convert hpoly using 1
  · funext z
    have hh := pbMass_splitTransfer q hij hil hjl heq k z
    change pbMass (splitTransfer q i j l z) k - pbMass q k =
      (q l - q i) * (C + q i * D) * z.2 - (C + q l * D) * z.1^2 -
      (C + q l * D) * z.1*z.2 - (C + q i * D) * z.2^2 + D*z.1^2*z.2 + D*z.1*z.2^2 at hh
    dsimp
    nlinarith only [hh]

/-- Three strictly interior lower coordinates allow all small split-and-transfer
moves while preserving the exact mean gap. -/
theorem splitTransfer_eventually_feasible {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hi0 : 0 < q i) (hj0 : 0 < q j) (hl0 : 0 < q l)
    (hi : q i < p i) (hj : q j < p j) (hl : q l < p l) :
    ∀ᶠ z in 𝓝 ((0, 0) : ℝ × ℝ), (p, splitTransfer q i j l z) ∈
      feasiblePairs n (meanGap p q) := by
  have hcoords : ∀ t : Fin n, ∀ᶠ z in 𝓝 ((0, 0) : ℝ × ℝ),
      0 ≤ splitTransfer q i j l z t ∧ splitTransfer q i j l z t ≤ p t := by
    intro t
    by_cases ht : t = i ∨ t = j ∨ t = l
    · have h0 : 0 < q t := by rcases ht with rfl | rfl | rfl <;> assumption
      have h1 : q t < p t := by rcases ht with rfl | rfl | rfl <;> assumption
      have hct : ContinuousAt (fun z ↦ splitTransfer q i j l z t) (0, 0) :=
        ((continuous_apply t).comp (continuous_splitTransfer q i j l)).continuousAt
      have he0 := continuousAt_const.eventually_lt hct (by simpa using h0)
      have he1 := hct.eventually_lt continuousAt_const (by simpa using h1)
      filter_upwards [he0, he1] with z hz0 hz1
      exact ⟨hz0.le, hz1.le⟩
    · push Not at ht
      exact Eventually.of_forall fun z ↦ by
        simpa [splitTransfer, Function.update_of_ne ht.1, Function.update_of_ne ht.2.1,
          Function.update_of_ne ht.2.2] using And.intro (h.2.1 t).1 (h.2.2 t)
  have hall := (eventually_all).mpr hcoords
  filter_upwards [hall] with z hz
  refine ⟨⟨h.1, ?_, ?_⟩, ?_⟩
  · intro t
    exact ⟨(hz t).1, (hz t).2.trans (h.1 t).2⟩
  · exact fun t ↦ (hz t).2
  · simp only [meanGap, sum_splitTransfer q hij hil hjl]

/-- A repeated smaller positive lower value is impossible at a constrained
local minimum, for a supporting randomized test on its exact active set
(QSPLIT). -/
theorem eq_of_repeated_smaller_at_localMin {p q : Fin n → ℝ}
    (h : AdmissiblePair p q)
    (hmin : IsLocalMinOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2)
      (feasiblePairs n (meanGap p q)) (p, q))
    {k : ℕ} (hk : 1 ≤ k) {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c)
    (hactive : (activeThresholds p q = {k} ∧ w = 1) ∨ activeThresholds p q = {k, k + 1})
    {i j l : Fin n} (hi0 : 0 < q i) (heq : q i = q j) (hlt : q i < q l)
    (hi : q i < p i) (hj : q j < p j) (hl : q l < p l)
    (hGi : randomizedGradient q w k i = c) (hGl : randomizedGradient q w k l = c) : i = j := by
  by_contra hij
  have hil : i ≠ l := fun hh ↦ hlt.ne (congrArg q hh)
  have hjl : j ≠ l := by intro hh; exact hlt.ne (heq.trans (congrArg q hh))
  let G : ℝ × ℝ → ℝ := fun z ↦ pbMass p k - pbMass (splitTransfer q i j l z) k
  let J : ℝ × ℝ → ℝ := fun z ↦ randomizedTail p w k - randomizedTail (splitTransfer q i j l z) w k
  let b := -(q l - q i) * (pbMassIntOn q ((univ.erase i).erase l) ((k : ℤ) - 2) -
      2 * pbMassIntOn q ((univ.erase i).erase l) ((k : ℤ) - 1) +
        pbMassIntOn q ((univ.erase i).erase l) k)
  let C := randomizedMixedCoefficient q w k i j
  let s0 := (((univ : Finset (Fin n)).erase i).erase j).erase l
  let D := randomizedCoefficientOn q s0 w (k - 1) - randomizedCoefficientOn q s0 w k
  have hb : b ≠ 0 := mass_tie_transfer_coefficient_ne_zero h.2.1 hc k hlt.ne hGi hGl
  have hG : HasStrictFDerivAt G (b • ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := by
    have hd := (hasStrictFDerivAt_pbMass_splitTransfer q hij hil hjl heq k).const_sub (pbMass p k)
    convert hd using 1
    dsimp [b]
    apply ContinuousLinearMap.ext
    intro z
    simp only [smul_apply, neg_apply, smul_eq_mul]
    ring
  have hC : C < 0 := randomizedMixedCoefficient_neg_of_repeated_smaller h.2.1 hw0 hw1 hc
    k hij heq hlt hGi hGl
  have hJ : ∀ z, J z = J (0, 0) + C*z.1^2 + z.1*z.2*(C-D*z.1-D*z.2) + z.2^2*0 := by
    intro z
    have hh := randomizedTail_splitTransfer q hij hil hjl heq hk hlt.ne hGi hGl z
    change randomizedTail (splitTransfer q i j l z) w k - randomizedTail q w k =
      -C*z.1^2-z.1*z.2*(C-D*z.1-D*z.2) at hh
    dsimp [J]
    rw [splitTransfer_zero]
    linarith
  obtain ⟨s, hs0, hs, htie, hdec⟩ := exists_tie_preserving_decreasing_curve hb hG hC
    (by fun_prop : ContinuousAt (fun z : ℝ × ℝ ↦ C-D*z.1-D*z.2) (0, 0))
    continuousAt_const hJ
  have hcurve : Tendsto (fun t ↦ (t, s t)) (𝓝 (0 : ℝ)) (𝓝 (0, 0)) := by
    exact tendsto_id.prodMk_nhds (by simpa [hs0] using hs.continuousAt.tendsto)
  let Q := fun t ↦ splitTransfer q i j l (t, s t)
  have hQ : Tendsto (fun t ↦ (p, Q t)) (𝓝 (0 : ℝ)) (𝓝 (p, q)) := by
    have hQt := (continuous_splitTransfer q i j l).continuousAt.tendsto.comp hcurve
    simpa only [Function.comp_def, splitTransfer_zero, Q] using tendsto_const_nhds.prodMk_nhds hQt
  have hfeas := (splitTransfer_eventually_feasible h hij hil hjl hi0
    (heq ▸ hi0) (hi0.trans hlt) hi hj hl).filter_mono hcurve
  have hwithin : Tendsto (fun t ↦ (p, Q t)) (𝓝[≠] (0 : ℝ))
      (𝓝[feasiblePairs n (meanGap p q)] (p, q)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hQ.mono_left nhdsWithin_le_nhds,
      hfeas.filter_mono nhdsWithin_le_nhds⟩
  have hle : ∀ᶠ t in 𝓝[≠] (0 : ℝ), tailObjective p q ≤ tailObjective p (Q t) :=
    hwithin.eventually hmin
  have hkm : k ∈ activeThresholds p q := by
    rcases hactive with ⟨hh, _⟩ | hh <;> simp [hh]
  have hkr : k ∈ Icc 1 n := mem_Icc.mpr ⟨hk, ((mem_activeThresholds p q k).mp hkm).2.1⟩
  have hbase : J (0, 0) = tailObjective p q := by
    dsimp [J]
    rw [splitTransfer_zero, randomizedDiff_eq]
    have he := ((mem_activeThresholds p q k).mp hkm).2.2
    rcases hactive with ⟨_, rfl⟩ | hh
    · simpa using he
    · have hk1 : k + 1 ∈ activeThresholds p q := by simp [hh]
      rw [he, ((mem_activeThresholds p q (k+1)).mp hk1).2.2]
      ring
  have hobj : ∀ᶠ t in 𝓝 (0 : ℝ), tailObjective p (Q t) = J (t, s t) := by
    rcases hactive with ⟨hh, hw⟩ | hh
    · have hloc := tailObjective_eventually_eq_max hkm hkr (by simp [hh])
      have he := hQ.eventually hloc
      filter_upwards [he] with t ht
      simpa [J, randomizedDiff_eq, hw] using ht
    · have hk1 : k + 1 ∈ activeThresholds p q := by simp [hh]
      have hk1r : k + 1 ∈ Icc 1 n := mem_Icc.mpr
        ⟨by omega, ((mem_activeThresholds p q (k+1)).mp hk1).2.1⟩
      have hloc := tailObjective_eventually_eq_max hkm hk1r (by rw [hh])
      have htie0 : G (0, 0) = 0 := by
        have hd := tailDiff_sub_succ p q k
        rw [((mem_activeThresholds p q k).mp hkm).2.2,
          ((mem_activeThresholds p q (k+1)).mp hk1).2.2] at hd
        simpa [G] using hd.symm
      filter_upwards [hQ.eventually hloc, htie] with t ht hgt
      have hmass : pbMass p k - pbMass (Q t) k = 0 := hgt.trans htie0
      have hdiff : tailDiff p (Q t) k = tailDiff p (Q t) (k+1) := by
        have hd := tailDiff_sub_succ p (Q t) k
        linarith
      rw [hdiff, max_self] at ht
      change tailObjective p (Q t) = randomizedTail p w k - randomizedTail (Q t) w k
      rw [ht, randomizedDiff_eq, hdiff]
      ring
  obtain ⟨t, ht⟩ := (hle.and (hdec.and (hobj.filter_mono nhdsWithin_le_nhds))).exists
  rw [ht.2.2, ← hbase] at ht
  exact not_lt_of_ge ht.1 ht.2.1

end

end PoissonBinomialComparison
