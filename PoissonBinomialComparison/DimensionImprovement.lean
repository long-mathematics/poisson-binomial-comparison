import PoissonBinomialComparison.SwitchRhoDensity
import PoissonBinomialComparison.SwitchMaximum
import PoissonBinomialComparison.CommonCoordinate
import PoissonBinomialComparison.Compactness
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Strict improvement after adjoining one coordinate

Adjoining the manuscript's common parameter `rho` leaves exactly one active
threshold. The prescribed fixed-gap perturbation decreases that threshold,
and continuity preserves its strict separation from the remaining thresholds.
-/

namespace PoissonBinomialComparison

open scoped BigOperators Topology
open Finset Filter

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

private theorem threshold_mem_of_tailDiff_pos (p q : Fin n → ℝ) (k : ℕ)
    (hk : 0 < tailDiff p q k) : k ∈ Icc 1 n := by
  by_cases hk0 : k = 0
  · simp [hk0, tailDiff] at hk
  have hkn : k ≤ n := by
    by_contra hnot
    have hnk : n < k := by omega
    simp [tailDiff, pbTail_eq_zero_of_lt p hnk, pbTail_eq_zero_of_lt q hnk] at hk
  exact mem_Icc.mpr ⟨by omega, hkn⟩

/-- A strictly interior common Bernoulli coordinate merges two adjacent active
thresholds into the unique threshold between them. -/
theorem activeThresholds_cons_common (h : AdmissiblePair p q) {j : ℕ}
    (hactive : activeThresholds p q = {j, j + 1})
    (hT : 0 < tailObjective p q) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    tailObjective (Fin.cons ρ p) (Fin.cons ρ q) = tailObjective p q ∧
      activeThresholds (Fin.cons ρ p) (Fin.cons ρ q) = {j + 1} := by
  have hjmem : j ∈ activeThresholds p q := by rw [hactive]; simp
  have hjmem' : j + 1 ∈ activeThresholds p q := by rw [hactive]; simp
  have hj := (mem_activeThresholds p q j).mp hjmem
  have hj' := (mem_activeThresholds p q (j + 1)).mp hjmem'
  have heq : tailDiff (Fin.cons ρ p) (Fin.cons ρ q) (j + 1) = tailObjective p q := by
    rw [tailDiff_cons_common, hj.2.2, hj'.2.2]
    ring
  have hmax : tailObjective (Fin.cons ρ p) (Fin.cons ρ q) = tailObjective p q := by
    apply le_antisymm (tailObjective_cons_common_le h ⟨hρ0.le, hρ1.le⟩)
    rw [← heq]
    exact tailDiff_le_tailObjective _ _ (mem_Icc.mpr ⟨by omega, by omega⟩)
  refine ⟨hmax, eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact (mem_activeThresholds _ _ (j + 1)).mpr ⟨by omega, by omega, heq.trans hmax.symm⟩
  · intro k hk
    have hk' := (mem_activeThresholds _ _ k).mp hk
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hnew := hk'.2.2
    rw [tailDiff_cons_common, hmax] at hnew
    have hl := tailDiff_le_tailObjective_all h l
    have hl' := tailDiff_le_tailObjective_all h (l + 1)
    have hleq : tailDiff p q l = tailObjective p q := by
      have hnonneg := mul_nonneg (sub_nonneg.mpr hρ1.le) (sub_nonneg.mpr hl')
      have he : ρ * (tailObjective p q - tailDiff p q l) ≤ 0 := by nlinarith
      have hzero : ρ * (tailObjective p q - tailDiff p q l) = 0 :=
        le_antisymm he (mul_nonneg hρ0.le (sub_nonneg.mpr hl))
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hρ0.ne')).symm
    have hleq' : tailDiff p q (l + 1) = tailObjective p q := by
      rw [hleq] at hnew
      have he : (1 - ρ) * (tailObjective p q - tailDiff p q (l + 1)) = 0 := by nlinarith
      exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (sub_pos.mpr hρ1).ne')).symm
    have hlmem : l ∈ activeThresholds p q := mem_filter.mpr
      ⟨threshold_mem_of_tailDiff_pos p q l (by rwa [hleq]), hleq⟩
    have hlmem' : l + 1 ∈ activeThresholds p q := mem_filter.mpr
      ⟨threshold_mem_of_tailDiff_pos p q (l + 1) (by rwa [hleq']), hleq'⟩
    rw [hactive] at hlmem hlmem'
    simp only [mem_insert, mem_singleton] at hlmem hlmem'
    omega

/-- A unique active threshold persists along any continuous parameter curve. -/
theorem tailObjective_curve_eventually_eq_of_unique {m k : ℕ}
    (P Q : ℝ → Fin m → ℝ) (hP : Continuous P) (hQ : Continuous Q) (t : ℝ)
    (hunique : activeThresholds (P t) (Q t) = {k}) :
    (fun u ↦ tailObjective (P u) (Q u)) =ᶠ[𝓝 t] (fun u ↦ tailDiff (P u) (Q u) k) := by
  have hk : k ∈ activeThresholds (P t) (Q t) := by rw [hunique]; simp
  have hk' := (mem_activeThresholds _ _ k).mp hk
  have hm : 0 < m := by omega
  have hc (l : ℕ) : Continuous (fun u ↦ tailDiff (P u) (Q u) l) := by fun_prop
  have hevent : ∀ᶠ u in 𝓝 t, ∀ l ∈ Icc 1 m, tailDiff (P u) (Q u) l ≤ tailDiff (P u) (Q u) k := by
    rw [eventually_all_finset]
    intro l hl
    by_cases hlk : l = k
    · subst l
      exact Eventually.of_forall (fun _ ↦ le_rfl)
    have hlt : tailDiff (P t) (Q t) l < tailDiff (P t) (Q t) k := by
      have hle := tailDiff_le_tailObjective (P t) (Q t) hl
      rw [← hk'.2.2] at hle
      apply lt_of_le_of_ne hle
      intro heq
      have hlmem : l ∈ activeThresholds (P t) (Q t) := mem_filter.mpr ⟨hl, heq.trans hk'.2.2⟩
      rw [hunique, mem_singleton] at hlmem
      exact hlk hlmem
    exact ((hc l).continuousAt.eventually_lt (hc k).continuousAt hlt).mono (fun _ ht ↦ ht.le)
  filter_upwards [hevent] with u hu
  apply le_antisymm
  · exact (tailObjective_le_iff _ _ hm _).mpr hu
  · exact tailDiff_le_tailObjective _ _ (mem_Icc.mpr ⟨hk'.1, hk'.2.1⟩)

/-- A negative derivative gives strict descent at all sufficiently small positive steps. -/
private theorem eventually_descends {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hneg : d < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε < f 0 := by
  have hs := hd.tendsto_slope_zero_right.eventually (eventually_lt_nhds hneg)
  have hp : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  filter_upwards [hs, hp] with ε hs hε
  simp only [zero_add, smul_eq_mul] at hs
  have hdiff : f ε - f 0 < 0 :=
    (mul_lt_mul_iff_right₀ (inv_pos.mpr hε)).mp (by simpa using hs)
  exact sub_neg.mp hdiff

/-- Upper parameter path in the manuscript's fixed-gap dimension perturbation. -/
def dimensionUpperPath (n : ℕ) (a ρ ε : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (ρ + ε / 2) (fun _ ↦ a - ε / (2 * n))

/-- Lower parameter path in the manuscript's fixed-gap dimension perturbation. -/
def dimensionLowerPath (n : ℕ) (b ρ ε : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (ρ - ε / 2) (fun _ ↦ b + ε / (2 * n))

@[fun_prop] theorem continuous_dimensionUpperPath (n : ℕ) (a ρ : ℝ) :
    Continuous (dimensionUpperPath n a ρ) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun _ ↦ ?_) i <;> simp [dimensionUpperPath] <;> fun_prop

@[fun_prop] theorem continuous_dimensionLowerPath (n : ℕ) (b ρ : ℝ) :
    Continuous (dimensionLowerPath n b ρ) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun _ ↦ ?_) i <;> simp [dimensionLowerPath] <;> fun_prop

/-- The perturbation preserves total mean gap exactly. -/
theorem meanGap_dimensionPath (n : ℕ) (hn : 0 < n) (a b ρ ε : ℝ) :
    meanGap (dimensionUpperPath n a ρ ε) (dimensionLowerPath n b ρ ε) = n * (a - b) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [dimensionUpperPath, dimensionLowerPath, meanGap, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- Chain rule for a homogeneous block with one separately varying coordinate. -/
theorem hasDerivAt_pbTail_cons_const_curve {n j : ℕ} (hj : 0 < j)
    {A R : ℝ → ℝ} {a ρ da dr : ℝ}
    (hA : HasDerivAt A da 0) (hR : HasDerivAt R dr 0)
    (ha : A 0 = a) (hr : R 0 = ρ) :
    HasDerivAt (fun ε ↦ pbTail (Fin.cons (R ε) (fun _ : Fin n ↦ A ε)) (j + 1))
      (dr * pbMass (fun _ : Fin n ↦ a) j + da * n *
        ((1 - ρ) * pbMass (fun _ : Fin (n - 1) ↦ a) j +
          ρ * pbMass (fun _ : Fin (n - 1) ↦ a) (j - 1))) 0 := by
  have hnext := (hasDerivAt_pbTail_const_succ n j (A 0)).comp 0 hA
  have hprev := (hasDerivAt_pbTail_const n j hj (A 0)).comp 0 hA
  have hd := (((hasDerivAt_const 0 (1 : ℝ)).sub hR).mul hnext).add (hR.mul hprev)
  convert hd using 1
  · funext ε
    exact pbTail_cons (fun _ : Fin n ↦ A ε) (R ε) j
  · simp only [Pi.sub_apply, Function.comp_apply, ha, hr, zero_sub]
    rw [← pbTail_sub_succ (fun _ : Fin n ↦ a) j]
    ring

/-- The exact active-tail derivative along the manuscript's perturbation. -/
theorem IsSwitch.hasDerivAt_dimensionPath {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (hj : 0 < j) (hjn : j < n) :
    HasDerivAt
      (fun ε ↦ tailDiff (dimensionUpperPath n a (switchRho n j a b) ε)
        (dimensionLowerPath n b (switchRho n j a b) ε) (j + 1))
      (pbMass (fun _ : Fin n ↦ a) j -
        (switchRhoDensity n j a b a + switchRhoDensity n j a b b) / 2) 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hA : HasDerivAt (fun ε : ℝ ↦ a - ε / (2 * n)) (-1 / (2 * n)) 0 := by
    convert (hasDerivAt_const 0 a).sub ((hasDerivAt_id 0).div_const (2 * (n : ℝ))) using 1 <;> first | rfl | ring
  have hB : HasDerivAt (fun ε : ℝ ↦ b + ε / (2 * n)) (1 / (2 * n)) 0 := by
    convert (hasDerivAt_const 0 b).add ((hasDerivAt_id 0).div_const (2 * (n : ℝ))) using 1 <;> first | rfl | ring
  have hRp : HasDerivAt (fun ε : ℝ ↦ switchRho n j a b + ε / 2) (1 / 2) 0 := by
    convert (hasDerivAt_const 0 (switchRho n j a b)).add ((hasDerivAt_id 0).div_const 2) using 1 <;> first | rfl | ring
  have hRq : HasDerivAt (fun ε : ℝ ↦ switchRho n j a b - ε / 2) (-1 / 2) 0 := by
    convert (hasDerivAt_const 0 (switchRho n j a b)).sub ((hasDerivAt_id 0).div_const 2) using 1 <;> first | rfl | ring
  have hp := hasDerivAt_pbTail_cons_const_curve (n := n) (a := a) (ρ := switchRho n j a b) hj hA hRp (by simp) (by simp)
  have hq := hasDerivAt_pbTail_cons_const_curve (n := n) (a := b) (ρ := switchRho n j a b) hj hB hRq (by simp) (by simp)
  convert hp.sub hq using 1
  · rfl
  · simp only [switchRhoDensity]
    rw [← h.pbMass_eq]
    field_simp
    ring

/-- Small positive perturbations remain admissible, including the newly opened
gap at the formerly common coordinate. -/
theorem dimensionPath_eventually_admissible {n : ℕ} {a b ρ : ℝ}
    (hb0 : 0 < b) (hba : b < a) (ha1 : a < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      AdmissiblePair (dimensionUpperPath n a ρ ε) (dimensionLowerPath n b ρ ε) := by
  have hR0 : ∀ᶠ ε : ℝ in 𝓝 0, 0 < ρ - ε / 2 :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hρ0)
  have hR1 : ∀ᶠ ε : ℝ in 𝓝 0, ρ + ε / 2 < 1 :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hρ1)
  have hB0 : ∀ᶠ ε : ℝ in 𝓝 0, 0 < b + ε / (2 * n) :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hb0)
  have hBA : ∀ᶠ ε : ℝ in 𝓝 0, b + ε / (2 * n) < a - ε / (2 * n) :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hba)
  have hA1 : ∀ᶠ ε : ℝ in 𝓝 0, a - ε / (2 * n) < 1 :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using ha1)
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  filter_upwards [hR0.filter_mono nhdsWithin_le_nhds, hR1.filter_mono nhdsWithin_le_nhds,
    hB0.filter_mono nhdsWithin_le_nhds, hBA.filter_mono nhdsWithin_le_nhds,
    hA1.filter_mono nhdsWithin_le_nhds, hpos] with ε hR0 hR1 hB0 hBA hA1 hε
  exact admissiblePair_cons ((admissiblePair_iff _ _).mpr (fun _ ↦ ⟨hB0.le, hBA.le, hA1.le⟩))
    hR0.le (by linarith) hR1.le

/-- A canonical interior switch admits the exact fixed-gap improving path from
the manuscript in one higher dimension. -/
theorem switch_dimension_improvement {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ ε : ℝ, 0 < ε ∧
      let a := switchUpper n j γ
      let b := switchLower n j γ
      let ρ := switchRho n j a b
      AdmissiblePair (dimensionUpperPath n a ρ ε) (dimensionLowerPath n b ρ ε) ∧
        meanGap (dimensionUpperPath n a ρ ε) (dimensionLowerPath n b ρ ε) = n * γ ∧
        tailObjective (dimensionUpperPath n a ρ ε) (dimensionLowerPath n b ρ ε) <
          switchValue n j γ := by
  let a := switchUpper n j γ
  let b := switchLower n j γ
  let ρ := switchRho n j a b
  let P := dimensionUpperPath n a ρ
  let Q := dimensionLowerPath n b ρ
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hρ := hs.switchRho_mem_Ioo hj hjn
  have hpq : AdmissiblePair (fun _ : Fin n ↦ a) (fun _ ↦ b) := switchPair_admissible hj hjn hγ0 hγ1
  have hT : 0 < tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) := by
    apply tailObjective_pos_of_meanGap_pos
    rw [meanGap_const, hs.2.2.2.1]
    exact mul_pos (by exact_mod_cast (show 0 < n by omega)) hγ0
  have hcommon := activeThresholds_cons_common hpq (hs.activeThresholds_eq hj hjn) hT hρ.1 hρ.2
  have hP0 : P 0 = Fin.cons ρ (fun _ : Fin n ↦ a) := by simp [P, dimensionUpperPath]
  have hQ0 : Q 0 = Fin.cons ρ (fun _ : Fin n ↦ b) := by simp [Q, dimensionLowerPath]
  have hunique : activeThresholds (P 0) (Q 0) = {j + 1} := by
    rw [hP0, hQ0]
    exact hcommon.2
  have hevent := tailObjective_curve_eventually_eq_of_unique P Q
    (continuous_dimensionUpperPath n a ρ) (continuous_dimensionLowerPath n b ρ) 0 hunique
  have hder := hs.hasDerivAt_dimensionPath hj hjn
  have hobj : HasDerivAt (fun ε ↦ tailObjective (P ε) (Q ε))
      (pbMass (fun _ : Fin n ↦ a) j -
        (switchRhoDensity n j a b a + switchRhoDensity n j a b b) / 2) 0 :=
    hder.congr_of_eventuallyEq hevent
  have hneg : pbMass (fun _ : Fin n ↦ a) j -
      (switchRhoDensity n j a b a + switchRhoDensity n j a b b) / 2 < 0 :=
    switchRhoDensity_improvement_neg hj hjn hγ0 hγ1
  have hdesc := eventually_descends hobj hneg
  have hfeasible := dimensionPath_eventually_admissible (n := n) hs.1 hs.2.1 hs.2.2.1 hρ.1 hρ.2
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hfeas, himprove⟩ := (hpos.and (hfeasible.and hdesc)).exists
  refine ⟨ε, hε, hfeas, ?_, ?_⟩
  · rw [meanGap_dimensionPath n (by omega), hs.2.2.2.1]
  · have hbase : tailObjective (P 0) (Q 0) = switchValue n j γ := by
      rw [hP0, hQ0, hcommon.1]
      exact tailObjective_switchPair hj hjn hγ0 hγ1
    exact himprove.trans_eq hbase

/-- At the maximal gap in dimension `n`, a strictly interior homogeneous pair
in dimension `n + 1` has the same gap and objective strictly below one. -/
theorem exists_dimension_endpoint_improvement (n : ℕ) (hn : 0 < n) :
    ∃ p q : Fin (n + 1) → ℝ, AdmissiblePair p q ∧ meanGap p q = n ∧
      tailObjective p q < 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  let γ : ℝ := n / (n + 1)
  let a : ℝ := (1 + γ) / 2
  let b : ℝ := (1 - γ) / 2
  have hγ0 : 0 < γ := div_pos hn0 hn1
  have hγ1 : γ < 1 := (div_lt_one hn1).mpr (by linarith)
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hba : b < a := by dsimp [a, b]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hp : ValidParameters (fun _ : Fin (n + 1) ↦ a) :=
    fun _ ↦ ⟨(hb0.trans hba).le, ha1.le⟩
  have hq : ValidParameters (fun _ : Fin (n + 1) ↦ b) :=
    fun _ ↦ ⟨hb0.le, (hba.trans ha1).le⟩
  refine ⟨(fun _ ↦ a), (fun _ ↦ b),
    (admissiblePair_iff _ _).mpr (fun _ ↦ ⟨hb0.le, hba.le, ha1.le⟩), ?_, ?_⟩
  · rw [meanGap_const]
    push_cast
    dsimp [a, b, γ]
    field_simp
    ring
  · apply (tailObjective_le_productTV _ _).trans_lt
      (productTV_lt_one_of_common_atom hp hq ∅ ?_ ?_)
    · simp [bernoulliWeight]
      exact pow_pos (sub_pos.mpr ha1) (n + 1)
    · simp [bernoulliWeight]
      exact pow_pos (sub_pos.mpr (hba.trans ha1)) (n + 1)

/-- Manuscript dimension-improvement lemma: the central benchmark in dimension
`n` is strictly improved by an admissible pair of the same gap in dimension `n+1`.
This statement uses no central-switch ordering or global minimization theorem. -/
theorem dimension_improvement {n : ℕ} (hn : 2 ≤ n) {Δ : ℝ}
    (hΔ0 : 0 < Δ) (hΔn : Δ ≤ n) :
    ∃ p q : Fin (n + 1) → ℝ, AdmissiblePair p q ∧ meanGap p q = Δ ∧
      tailObjective p q < benchmark n Δ := by
  rcases hΔn.eq_or_lt with heq | hlt
  · subst Δ
    simpa only [benchmark_at_dimension (show 0 < n by omega)] using
      exists_dimension_endpoint_improvement n (by omega)
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hj : 0 < n / 2 := by omega
    have hjn : n / 2 < n := by omega
    have hγ0 : 0 < Δ / n := div_pos hΔ0 hn0
    have hγ1 : Δ / n < 1 := (div_lt_one hn0).mpr hlt
    obtain ⟨ε, _, hfeasible, hgap, himprove⟩ :=
      switch_dimension_improvement hj hjn hγ0 hγ1
    refine ⟨_, _, hfeasible, ?_, ?_⟩
    · rw [hgap]
      field_simp
    · rw [benchmark_eq_switchValue hΔ0 hlt]
      exact himprove

end

end PoissonBinomialComparison
