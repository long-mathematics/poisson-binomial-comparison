import PoissonBinomialComparison.SwitchMaximum
import PoissonBinomialComparison.Compactness
import PoissonBinomialComparison.Reflection
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Homogeneous minimizers occur at switches

At a fixed interior parameter gap, each individual threshold difference has no
interior local minimum. A unique active threshold persists locally, so an
interior local minimum of the finite maximum must have two adjacent active
thresholds and hence satisfy the switch equation.
-/

namespace PoissonBinomialComparison

open scoped BigOperators Topology
open Finset Filter

noncomputable section

/-- One homogeneous threshold difference as a function of the lower parameter. -/
def homogeneousTailDiff (n : ℕ) (γ : ℝ) (k : ℕ) (b : ℝ) : ℝ :=
  tailDiff (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) k

/-- The homogeneous objective at fixed coordinate gap. -/
def homogeneousObjective (n : ℕ) (γ b : ℝ) : ℝ :=
  tailObjective (fun _ : Fin n ↦ b + γ) (fun _ ↦ b)

@[fun_prop] theorem continuous_homogeneousTailDiff (n k : ℕ) (γ : ℝ) :
    Continuous (homogeneousTailDiff n γ k) := by
  unfold homogeneousTailDiff
  fun_prop

@[fun_prop] theorem continuous_homogeneousObjective (n : ℕ) (γ : ℝ) :
    Continuous (homogeneousObjective n γ) := by
  unfold homogeneousObjective
  fun_prop

/-- Derivative with respect to a simultaneous shift of the two parameters. -/
theorem hasDerivAt_homogeneousTailDiff (n k : ℕ) (γ b : ℝ) :
    HasDerivAt (homogeneousTailDiff n γ (k + 1))
      ((n : ℝ) * (pbMass (fun _ : Fin (n - 1) ↦ b + γ) k -
        pbMass (fun _ : Fin (n - 1) ↦ b) k)) b := by
  have h := ((hasDerivAt_pbTail_const_succ n k (b + γ)).comp b
    ((hasDerivAt_id b).add_const γ)).sub (hasDerivAt_pbTail_const_succ n k b)
  convert h using 1
  · rfl
  · ring

/-- Positive homogeneous masses at every count in the support range. -/
theorem pbMass_const_pos_of_interior (m k : ℕ) (hk : k ≤ m) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) : 0 < pbMass (fun _ : Fin m ↦ b) k := by
  rw [pbMass_const]
  have hc : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hk
  exact mul_pos (mul_pos hc (pow_pos hb0 _)) (pow_pos (sub_pos.mpr hb1) _)

private theorem density_ratio_strictAntiOn {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ m)
    {γ : ℝ} (hγ : 0 < γ) :
    StrictAntiOn
      (fun b : ℝ ↦ ((b + γ) / b) ^ k * ((1 - (b + γ)) / (1 - b)) ^ (m - k))
      (Set.Ioo 0 (1 - γ)) := by
  intro b₁ hb₁ b₂ hb₂ hlt
  have hb₁' : 0 < 1 - b₁ := by linarith [hb₁.2]
  have hb₂' : 0 < 1 - b₂ := by linarith [hb₂.2]
  have hr₁ : (b₂ + γ) / b₂ < (b₁ + γ) / b₁ := by
    apply (div_lt_div_iff₀ hb₂.1 hb₁.1).2
    nlinarith
  have hr₂ : (1 - (b₂ + γ)) / (1 - b₂) <
      (1 - (b₁ + γ)) / (1 - b₁) := by
    apply (div_lt_div_iff₀ hb₂' hb₁').2
    nlinarith
  have hp₁ : 0 < (b₂ + γ) / b₂ := div_pos (by linarith [hb₂.1]) hb₂.1
  have hp₂ : 0 < (1 - (b₁ + γ)) / (1 - b₁) :=
    div_pos (by linarith [hb₁.2]) hb₁'
  have hp₂' : 0 < (1 - (b₂ + γ)) / (1 - b₂) :=
    div_pos (by linarith [hb₂.2]) hb₂'
  by_cases hk0 : k = 0
  · subst k
    simpa using pow_lt_pow_left₀ hr₂ hp₂'.le (by omega : m ≠ 0)
  · calc
      _ ≤ ((b₂ + γ) / b₂) ^ k * ((1 - (b₁ + γ)) / (1 - b₁)) ^ (m - k) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp₂'.le hr₂.le _) (pow_nonneg hp₁.le _)
      _ < _ := mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hr₁ hp₁.le hk0) (pow_pos hp₂ _)

private theorem density_ratio_eq {m k : ℕ} (hk : k ≤ m) {γ b : ℝ}
    (hb : b ∈ Set.Ioo 0 (1 - γ)) (hγ : 0 < γ) :
    pbMass (fun _ : Fin m ↦ b + γ) k / pbMass (fun _ : Fin m ↦ b) k =
      ((b + γ) / b) ^ k * ((1 - (b + γ)) / (1 - b)) ^ (m - k) := by
  have hc : (m.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hb1 : 1 - b ≠ 0 := ne_of_gt (by linarith [hb.2] : 0 < 1 - b)
  rw [pbMass_const, pbMass_const]
  simp only [div_pow]
  field_simp [hc, hb.1.ne', hb1]

/-- At an interior critical point, every point to its left in the feasible
interior has a strictly smaller individual threshold difference. -/
theorem homogeneousTailDiff_lt_at_critical {n k : ℕ} (hn : 2 ≤ n) (hk : k < n)
    {γ b x : ℝ} (hγ : 0 < γ) (hb : b ∈ Set.Ioo 0 (1 - γ))
    (hx0 : 0 < x) (hxb : x < b)
    (hcrit : deriv (homogeneousTailDiff n γ (k + 1)) b = 0) :
    homogeneousTailDiff n γ (k + 1) x < homogeneousTailDiff n γ (k + 1) b := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkp : k ≤ n - 1 := by omega
  have hmasspos := pbMass_const_pos_of_interior (n - 1) k hkp hb.1 (by linarith [hb.2])
  have hmass : pbMass (fun _ : Fin (n - 1) ↦ b + γ) k =
      pbMass (fun _ : Fin (n - 1) ↦ b) k := by
    rw [(hasDerivAt_homogeneousTailDiff n k γ b).deriv] at hcrit
    rcases mul_eq_zero.mp hcrit with hz | hz
    · exact False.elim (hnpos.ne' hz)
    · exact sub_eq_zero.mp hz
  have hratio : ((b + γ) / b) ^ k * ((1 - (b + γ)) / (1 - b)) ^ (n - 1 - k) = 1 := by
    rw [← density_ratio_eq hkp hb hγ, hmass, div_self hmasspos.ne']
  have hmono : StrictMonoOn (homogeneousTailDiff n γ (k + 1)) (Set.Icc x b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc x b)
      (continuous_homogeneousTailDiff n (k + 1) γ).continuousOn
    intro t ht
    rw [interior_Icc] at ht
    have ht' : t ∈ Set.Ioo 0 (1 - γ) := ⟨hx0.trans ht.1, ht.2.trans hb.2⟩
    have hrat := density_ratio_strictAntiOn (by omega : 1 ≤ n - 1) hkp hγ ht' hb ht.2
    dsimp only at hrat
    rw [hratio, ← density_ratio_eq hkp ht' hγ] at hrat
    have hden := pbMass_const_pos_of_interior (n - 1) k hkp ht'.1 (by linarith [ht'.2])
    have hdiff : 0 < pbMass (fun _ : Fin (n - 1) ↦ t + γ) k -
        pbMass (fun _ : Fin (n - 1) ↦ t) k := by
      have hgt := (one_lt_div hden).mp hrat
      linarith
    rw [(hasDerivAt_homogeneousTailDiff n k γ t).deriv]
    exact mul_pos hnpos hdiff
  exact hmono ⟨le_rfl, hxb.le⟩ ⟨hxb.le, le_rfl⟩ hxb

/-- No individual positive-threshold difference has an interior local minimum. -/
theorem not_isLocalMin_homogeneousTailDiff {n k : ℕ} (hn : 2 ≤ n) (hk : k < n)
    {γ b : ℝ} (hγ : 0 < γ) (hb : b ∈ Set.Ioo 0 (1 - γ)) :
    ¬IsLocalMin (homogeneousTailDiff n γ (k + 1)) b := by
  intro hmin
  have hcrit := hmin.deriv_eq_zero
  obtain ⟨l, u, hb', hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hmin
  obtain ⟨x, hx, hxb⟩ := exists_between (max_lt hb.1 hb'.1)
  have hx0 : 0 < x := (le_max_left 0 l).trans_lt hx
  have hxl : l < x := (le_max_right 0 l).trans_lt hx
  have hlow := hsub ⟨hxl, hxb.trans hb'.2⟩
  exact not_lt_of_ge hlow (homogeneousTailDiff_lt_at_critical hn hk hγ hb hx0 hxb hcrit)

/-- A uniquely active threshold remains the maximum on a neighborhood. -/
theorem homogeneousObjective_eventually_eq_of_unique {n k : ℕ} {γ b : ℝ}
    (hunique : activeThresholds (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) = {k}) :
    homogeneousObjective n γ =ᶠ[𝓝 b] homogeneousTailDiff n γ k := by
  have hk : k ∈ activeThresholds (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) := by rw [hunique]; simp
  have hk' := (mem_activeThresholds _ _ k).mp hk
  have hn : 0 < n := by omega
  have hevent : ∀ᶠ t in 𝓝 b, ∀ l ∈ Icc 1 n,
      homogeneousTailDiff n γ l t ≤ homogeneousTailDiff n γ k t := by
    rw [eventually_all_finset]
    intro l hl
    by_cases hlk : l = k
    · subst l
      exact Eventually.of_forall (fun _ ↦ le_rfl)
    have hlt : homogeneousTailDiff n γ l b < homogeneousTailDiff n γ k b := by
      have hle := tailDiff_le_tailObjective (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) hl
      rw [← hk'.2.2] at hle
      apply lt_of_le_of_ne hle
      intro heq
      have hlmem : l ∈ activeThresholds (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) :=
        mem_filter.mpr ⟨hl, heq.trans hk'.2.2⟩
      rw [hunique, mem_singleton] at hlmem
      exact hlk hlmem
    exact ((continuous_homogeneousTailDiff n l γ).continuousAt.eventually_lt
      (continuous_homogeneousTailDiff n k γ).continuousAt hlt).mono (fun _ ht ↦ ht.le)
  filter_upwards [hevent] with t ht
  apply le_antisymm
  · exact (tailObjective_le_iff _ _ hn _).mpr ht
  · exact tailDiff_le_tailObjective _ _ (mem_Icc.mpr ⟨hk'.1, hk'.2.1⟩)

/-- Every interior local homogeneous minimizer is an interior switch at one of
the manuscript's nonendpoint counts. -/
theorem homogeneous_localMin_is_switch {n : ℕ} (hn : 2 ≤ n) {γ b : ℝ}
    (hγ : 0 < γ) (hb : b ∈ Set.Ioo 0 (1 - γ))
    (hmin : IsLocalMin (homogeneousObjective n γ) b) :
    ∃ j, 1 ≤ j ∧ j < n ∧ IsSwitch n j γ (b + γ) b := by
  have hpq : AdmissiblePair (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) :=
    (admissiblePair_iff _ _).mpr (fun _ ↦ ⟨hb.1.le, by linarith, by linarith [hb.2]⟩)
  have hgap : 0 < meanGap (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) := by
    rw [meanGap_const]
    exact mul_pos (by exact_mod_cast (show 0 < n by omega)) (by linarith)
  have hT : tailObjective (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) < 1 := by
    apply (tailObjective_le_productTV _ _).trans_lt
      (productTV_lt_one_of_common_atom hpq.1 hpq.2.1 ∅ ?_ ?_)
    · simp [bernoulliWeight]
      exact pow_pos (by linarith [hb.2]) n
    · simp [bernoulliWeight]
      exact pow_pos (by linarith [hb.2]) n
  obtain ⟨j, hj, hjn, hactive⟩ := activeThresholds_singleton_or_adjacent hpq hgap hT
  rcases hactive with hsingle | ⟨hjnext, hpair⟩
  · have hlocal := hmin.congr (homogeneousObjective_eventually_eq_of_unique hsingle)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact False.elim (not_isLocalMin_homogeneousTailDiff hn (by omega) hγ hb hlocal)
  · refine ⟨j, hj, by omega, hb.1, by linarith, by linarith [hb.2], by ring, ?_⟩
    have hjmem : j ∈ activeThresholds (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) := by
      rw [hpair]; simp
    have hjmem' : j + 1 ∈ activeThresholds (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) := by
      rw [hpair]; simp
    have heq := (mem_activeThresholds _ _ j).mp hjmem |>.2.2
    have heq' := (mem_activeThresholds _ _ (j + 1)).mp hjmem' |>.2.2
    have hd := tailDiff_sub_succ (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) j
    have hm : pbMass (fun _ : Fin n ↦ b + γ) j = pbMass (fun _ : Fin n ↦ b) j := by
      linarith
    exact (pbMass_const_eq_iff hjn (b + γ) b).mp hm

/-- Relative local minimizers in the feasible interval satisfy the same switch
equation whenever their lower parameter is interior. -/
theorem homogeneous_localMinOn_interior_is_switch {n : ℕ} (hn : 2 ≤ n) {γ b : ℝ}
    (hγ : 0 < γ) (hb : b ∈ Set.Ioo 0 (1 - γ))
    (hmin : IsLocalMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) b) :
    ∃ j, 1 ≤ j ∧ j < n ∧ IsSwitch n j γ (b + γ) b :=
  homogeneous_localMin_is_switch hn hγ hb (hmin.isLocalMin (Icc_mem_nhds hb.1 hb.2))

/-- Upper tails decrease with their threshold for valid parameters. -/
theorem pbTail_antitone {n : ℕ} {p : Fin n → ℝ} (hp : ValidParameters p) :
    Antitone (pbTail p) := by
  intro k l hkl
  rw [pbTail_eq_sum_mass, pbTail_eq_sum_mass]
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact mem_Icc.mpr ⟨hkl.trans (mem_Icc.mp hj).1, (mem_Icc.mp hj).2⟩
  · intro j _ _
    exact pbMass_nonneg hp j

/-- The left feasible endpoint has the unique active threshold one. -/
theorem homogeneous_activeThresholds_left {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    activeThresholds (fun _ : Fin n ↦ 0 + γ) (fun _ ↦ (0 : ℝ)) = {1} := by
  have hp : ValidParameters (fun _ : Fin n ↦ γ) := fun _ ↦ ⟨hγ0.le, hγ1.le⟩
  have hd (k : ℕ) (hk : 1 ≤ k) :
      tailDiff (fun _ : Fin n ↦ 0 + γ) (fun _ ↦ 0) k = pbTail (fun _ : Fin n ↦ γ) k := by
    simp [tailDiff, pbTail_const_zero, show k ≠ 0 by omega]
  have hmax : tailObjective (fun _ : Fin n ↦ 0 + γ) (fun _ ↦ 0) =
      pbTail (fun _ : Fin n ↦ γ) 1 := by
    apply le_antisymm
    · rw [tailObjective_le_iff _ _ (by omega)]
      intro k hk
      rw [hd k (mem_Icc.mp hk).1]
      exact pbTail_antitone hp (mem_Icc.mp hk).1
    · rw [← hd 1 le_rfl]
      exact tailDiff_le_tailObjective _ _ (mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hstrict : pbTail (fun _ : Fin n ↦ γ) 2 < pbTail (fun _ : Fin n ↦ γ) 1 := by
    have hmass := pbMass_const_pos_of_interior n 1 (by omega) hγ0 hγ1
    have htail := pbTail_sub_succ (fun _ : Fin n ↦ γ) 1
    linarith
  apply eq_singleton_iff_unique_mem.mpr
  constructor
  · exact (mem_activeThresholds _ _ 1).mpr ⟨le_rfl, by omega, (hd 1 le_rfl).trans hmax.symm⟩
  · intro k hk
    have hk' := (mem_activeThresholds _ _ k).mp hk
    by_contra hk1
    have hge : 2 ≤ k := by omega
    have hlt := (pbTail_antitone hp hge).trans_lt hstrict
    rw [← hd k hk'.1, hk'.2.2, hmax] at hlt
    exact lt_irrefl _ hlt

private theorem nonneg_derivative_of_localMinOn_left {f : ℝ → ℝ} {d a b : ℝ}
    (hab : a < b) (hmin : IsLocalMinOn f (Set.Icc a b) a) (hd : HasDerivAt f d a) : 0 ≤ d := by
  have htan : (1 : ℝ) ∈ posTangentConeAt (Set.Icc a b) a := by
    apply mem_posTangentConeAt_of_frequently_mem
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < b - a :=
      nhdsWithin_le_nhds (eventually_lt_nhds (sub_pos.mpr hab))
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    apply Eventually.frequently
    filter_upwards [hsmall, hpos] with t ht ht0
    simp only [smul_eq_mul, mul_one, Set.mem_Icc]
    constructor <;> linarith
  have h := hmin.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt htan
  simpa using h

/-- The negative derivative of the uniquely active first threshold excludes
the left feasible endpoint from all relative local homogeneous minima. -/
theorem not_isLocalMinOn_homogeneousObjective_left {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ¬IsLocalMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) 0 := by
  intro hmin
  have hunique := homogeneous_activeThresholds_left hn hγ0 hγ1
  have hevent := homogeneousObjective_eventually_eq_of_unique hunique
  have hlocal := hmin.congr (hevent.filter_mono nhdsWithin_le_nhds)
    (show (0 : ℝ) ∈ Set.Icc 0 (1 - γ) from ⟨le_rfl, by linarith⟩)
  have hder := hasDerivAt_homogeneousTailDiff n 0 γ 0
  have hnonneg := nonneg_derivative_of_localMinOn_left (by linarith : (0 : ℝ) < 1 - γ) hlocal hder
  simp only [zero_add, pbMass_zero, prod_const, card_univ, Fintype.card_fin, sub_zero, one_pow] at hnonneg
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (1 - γ) ^ (n - 1) < (1 : ℝ) :=
    pow_lt_one₀ (by linarith) (by linarith) (by omega)
  exact not_lt_of_ge hnonneg (mul_neg_of_pos_of_neg hnpos (sub_neg.mpr hp))

/-- Reflection exchanges the two feasible homogeneous endpoints. -/
theorem homogeneousObjective_reflection (n : ℕ) (γ b : ℝ) :
    homogeneousObjective n γ (1 - γ - b) = homogeneousObjective n γ b := by
  unfold homogeneousObjective
  have hp : (fun _ : Fin n ↦ 1 - γ - b + γ) = (fun _ ↦ 1 - b) := by funext i; ring
  have hq : (fun _ : Fin n ↦ 1 - γ - b) = (fun _ ↦ 1 - (b + γ)) := by funext i; ring
  rw [hp, hq]
  exact tailObjective_reflection (fun _ : Fin n ↦ b + γ) (fun _ ↦ b)

/-- The right feasible endpoint is excluded by reflection of the left endpoint. -/
theorem not_isLocalMinOn_homogeneousObjective_right {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ¬IsLocalMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) (1 - γ) := by
  intro hmin
  let g : ℝ → ℝ := fun t ↦ 1 - γ - t
  have hmin' : IsLocalMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) (g 0) := by
    simpa [g] using hmin
  have hmap : Set.Icc 0 (1 - γ) ⊆ g ⁻¹' Set.Icc 0 (1 - γ) := by
    intro t ht
    change 0 ≤ 1 - γ - t ∧ 1 - γ - t ≤ 1 - γ
    constructor <;> linarith [ht.1, ht.2]
  have hcomp := hmin'.comp_continuousOn hmap (by fun_prop : ContinuousOn g (Set.Icc 0 (1 - γ)))
    (show (0 : ℝ) ∈ Set.Icc 0 (1 - γ) from ⟨le_rfl, by linarith⟩)
  have heq : homogeneousObjective n γ ∘ g = homogeneousObjective n γ := by
    funext t
    exact homogeneousObjective_reflection n γ t
  rw [heq] at hcomp
  exact not_isLocalMinOn_homogeneousObjective_left hn hγ0 hγ1 hcomp

/-- Every feasible relative local homogeneous minimizer is interior and is a
switch. This includes the exclusion of both endpoints of the feasible interval. -/
theorem homogeneous_localMinOn_is_switch {n : ℕ} (hn : 2 ≤ n) {γ b : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : b ∈ Set.Icc 0 (1 - γ))
    (hmin : IsLocalMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) b) :
    ∃ j, 1 ≤ j ∧ j < n ∧ IsSwitch n j γ (b + γ) b := by
  have hb0 : 0 < b := by
    apply lt_of_le_of_ne hb.1
    intro heq
    subst b
    exact not_isLocalMinOn_homogeneousObjective_left hn hγ0 hγ1 hmin
  have hb1 : b < 1 - γ := by
    apply lt_of_le_of_ne hb.2
    intro heq
    rw [heq] at hmin
    exact not_isLocalMinOn_homogeneousObjective_right hn hγ0 hγ1 hmin
  exact homogeneous_localMinOn_interior_is_switch hn hγ0 ⟨hb0, hb1⟩ hmin

/-- In particular, every global homogeneous minimizer is an interior switch. -/
theorem homogeneous_minimizer_is_switch {n : ℕ} (hn : 2 ≤ n) {γ b : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : b ∈ Set.Icc 0 (1 - γ))
    (hmin : IsMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) b) :
    ∃ j, 1 ≤ j ∧ j < n ∧ IsSwitch n j γ (b + γ) b :=
  homogeneous_localMinOn_is_switch hn hγ0 hγ1 hb hmin.isLocalMinOn

/-- A homogeneous global minimum exists and is attained at an interior switch. -/
theorem exists_homogeneous_minimizing_switch {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ j b, 1 ≤ j ∧ j < n ∧ IsSwitch n j γ (b + γ) b ∧
      IsMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) b := by
  obtain ⟨b, hb, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by linarith : (0 : ℝ) ≤ 1 - γ))
    (continuous_homogeneousObjective n γ).continuousOn
  obtain ⟨j, hj, hjn, hswitch⟩ := homogeneous_minimizer_is_switch hn hγ0 hγ1 hb hmin
  exact ⟨j, b, hj, hjn, hswitch, hmin⟩

end

end PoissonBinomialComparison
