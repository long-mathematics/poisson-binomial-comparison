import PoissonBinomialComparison.DeletionObjective
import PoissonBinomialComparison.DeletionMixture
import PoissonBinomialComparison.BenchmarkConcavity
import PoissonBinomialComparison.DimensionImprovement
import PoissonBinomialComparison.HomogeneousMinimum
import Mathlib.Analysis.MeanInequalities

/-! # Initial boundary reductions for a global minimizer

The only induction hypothesis used here is the lower bound in dimension `n-1`.
-/

namespace PoissonBinomialComparison

open Finset Set
open scoped BigOperators

/-- Global minimality among admissible pairs with the same total mean gap. -/
def IsGapMinimizer {n : ℕ} (p q : Fin n → ℝ) : Prop :=
  ∀ r s : Fin n → ℝ, AdmissiblePair r s → meanGap r s = meanGap p q →
    tailObjective p q ≤ tailObjective r s

/-- A global fixed-gap minimum supplies the local minimum used in stationarity. -/
theorem IsGapMinimizer.isLocalMinOn {n : ℕ} {p q : Fin n → ℝ} (hm : IsGapMinimizer p q) :
    IsLocalMinOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) => tailObjective x.1 x.2)
      (feasiblePairs n (meanGap p q)) (p,q) := by
  apply IsMinOn.isLocalMinOn
  intro x hx
  exact hm x.1 x.2 hx.1 hx.2

/-- Comparison with the explicit central homogeneous competitor. -/
theorem IsGapMinimizer.le_benchmark {n : ℕ} (hn : 2 ≤ n) {p q : Fin n → ℝ}
    (hm : IsGapMinimizer p q) (hgap0 : 0 < meanGap p q) (hgapn : meanGap p q < n) :
    tailObjective p q ≤ benchmark n (meanGap p q) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hj : 0 < n / 2 := by omega
  have hjn : n / 2 < n := by omega
  have hg0 : 0 < meanGap p q / n := div_pos hgap0 hn0
  have hg1 : meanGap p q / n < 1 := (div_lt_one hn0).mpr hgapn
  have hh := hm _ _ (switchPair_admissible hj hjn hg0 hg1)
    (show meanGap (fun _ : Fin n => switchUpper n (n/2) (meanGap p q/n))
      (fun _ => switchLower n (n/2) (meanGap p q/n)) = meanGap p q by
      rw [meanGap_switchPair hj hjn hg0 hg1]; field_simp)
  rw [tailObjective_switchPair hj hjn hg0 hg1, ← benchmark_eq_switchValue hgap0 hgapn] at hh
  exact hh

/-- A minimizing interior-gap pair has at least three strictly changing coordinates. -/
theorem IsGapMinimizer.three_le_positiveGapCoordinates {n : ℕ} (hn : 3 ≤ n)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hgap0 : 0 < meanGap p q) (hgapn : meanGap p q < n) :
    3 ≤ (positiveGapCoordinates p q).card := by
  by_contra hc
  have hlow := two_gap_lower_bound (by omega : 1 ≤ n) h (by omega)
  have hupp := hm.le_benchmark (by omega) hgap0 hgapn
  have hstrict := (benchmark_strict_bounds hn hgap0 hgapn).2.trans_le (min_le_left _ _)
  linarith

/-- The objective of an interior-gap minimizer is strictly less than one. -/
theorem IsGapMinimizer.tailObjective_lt_one {n : ℕ} (hn : 3 ≤ n)
    {p q : Fin n → ℝ} (hm : IsGapMinimizer p q)
    (hgap0 : 0 < meanGap p q) (hgapn : meanGap p q < n) : tailObjective p q < 1 :=
  (hm.le_benchmark (by omega) hgap0 hgapn).trans_lt
    ((benchmark_strict_bounds hn hgap0 hgapn).2.trans_le (min_le_right _ _))

/-- The dimension-improvement competitor excludes every common deterministic coordinate. -/
theorem IsGapMinimizer.no_common_deterministic {n : ℕ} (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hgap0 : 0 < meanGap p q) (i : Fin n) (heq : p i = q i) :
    p i ≠ 0 ∧ p i ≠ 1 := by
  have hfalse (hd : p i = 0 ∨ p i = 1) : False := by
    obtain ⟨r,s,hrs,hgap,hobj⟩ := exists_deleted_deterministic_pair (by omega) h i heq hd
    have hlow := hind r s hrs
    rw [hgap,hobj] at hlow
    have hbound := meanGap_le_dimension hrs
    rw [hgap] at hbound
    have himprove := dimension_improvement (by omega : 2 ≤ n-1) hgap0 hbound
    have hn' : n-1+1 = n := by omega
    rw [hn'] at himprove
    obtain ⟨r',s',hrs',hgap',hobj'⟩ := himprove
    have hmin := hm r' s' hrs' hgap'
    linarith
  exact ⟨fun hz => hfalse (Or.inl hz), fun ho => hfalse (Or.inr ho)⟩

/-- Every upper parameter is positive and every lower parameter is below one. -/
theorem IsGapMinimizer.parameter_bounds {n : ℕ} (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hgap0 : 0 < meanGap p q) : ∀ i, 0 < p i ∧ q i < 1 := by
  intro i
  have hp := h.1 i
  have hq := h.2.1 i
  have hqp := h.2.2 i
  constructor
  · by_contra hz
    have hp0 : p i = 0 := by linarith
    have heq : p i = q i := by linarith
    exact (hm.no_common_deterministic hn hind h hgap0 i heq).1 hp0
  · by_contra ho
    have hp1 : p i = 1 := by linarith
    have heq : p i = q i := by linarith
    exact (hm.no_common_deterministic hn hind h hgap0 i heq).2 hp1

/-- Reflection preserves fixed-gap global minimality. -/
theorem IsGapMinimizer.reflection {n : ℕ} {p q : Fin n → ℝ} (hm : IsGapMinimizer p q) :
    IsGapMinimizer (fun i => 1-q i) (fun i => 1-p i) := by
  intro r s h hgap
  rw [meanGap_reflection] at hgap
  have hh := hm _ _ (admissiblePair_reflection h)
    (by rw [meanGap_reflection]; exact hgap)
  simpa only [tailObjective_reflection] using hh

/-- The uppermost count mass is the product of all Bernoulli parameters. -/
theorem pbTail_at_dimension (n : ℕ) (p : Fin n → ℝ) : pbTail p n = ∏ i, p i := by
  rw [pbTail_eq_sum_mass]
  simp only [Finset.Icc_self, sum_singleton]
  unfold pbMass pbMassOn
  have hs : (univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using powersetCard_self (univ : Finset (Fin n))
  rw [hs]
  simp [bernoulliWeight]

/-- An all-one upper vector gives an exact product formula for the objective. -/
theorem tailObjective_one_left {n : ℕ} (hn : 0 < n) {q : Fin n → ℝ}
    (hq : ValidParameters q) :
    tailObjective (fun _ : Fin n => 1) q = 1 - ∏ i, q i := by
  have hd : tailDiff (fun _ : Fin n => 1) q n = 1 - ∏ i, q i := by
    simp [tailDiff, pbTail_at_dimension]
  apply le_antisymm
  · apply (tailObjective_le_iff _ _ hn _).mpr
    intro k hk
    have hkn := (mem_Icc.mp hk).2
    simp only [tailDiff, pbTail_const_one, ite_eq_left hkn]
    rw [← pbTail_at_dimension n q]
    exact sub_le_sub_left (pbTail_antitone hq hkn) 1
  · rw [← hd]
    exact tailDiff_le_tailObjective _ _ (mem_Icc.mpr ⟨hn,le_rfl⟩)

/-- The finite AM-GM inequality in the product form needed for endpoint vectors. -/
theorem product_le_mean_pow {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) : (∏ i, q i) ≤ ((∑ i, q i) / n)^n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmean := Real.geom_mean_le_arith_mean_weighted univ
    (fun _ : Fin n => (1 : ℝ)/n) q (fun _ _ => by positivity)
    (by simp [hn0.ne']) (fun i _ => hq i)
  have hp := pow_le_pow_left₀ (prod_nonneg (fun i _ => Real.rpow_nonneg (hq i) _)) hmean n
  rw [← Finset.prod_pow] at hp
  have hpow (i : Fin n) : (q i ^ ((1 : ℝ)/n))^n = q i := by
    rw [← Real.rpow_mul_natCast (hq i), one_div_mul_cancel hn0.ne', Real.rpow_one]
  simp only [hpow] at hp
  have hsum : (∑ i : Fin n, (1 : ℝ)/n * q i) = (∑ i, q i)/n := by
    rw [← mul_sum]
    ring
  rwa [hsum] at hp

/-- The homogeneous endpoint value is strictly above the benchmark. -/
theorem benchmark_lt_homogeneous_one_left {n : ℕ} (hn : 2 ≤ n) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) :
    benchmark n (n * (1-b)) < tailObjective (fun _ : Fin n => 1) (fun _ => b) := by
  have hle := homogeneous_minimum hn hb0.le hb1.le (a := 1) le_rfl
  apply lt_of_le_of_ne hle
  intro he
  have hh := (homogeneous_minimum_eq_iff hn hb0.le (a := 1) le_rfl
    (by linarith) (by linarith)).mp he.symm
  rcases hh with hh | hh <;> exact (lt_irrefl (1 : ℝ)) hh.2.2.1

/-- A global interior-gap minimizer cannot have every upper parameter equal to one. -/
theorem IsGapMinimizer.upper_ne_one {n : ℕ} (hn : 3 ≤ n) {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hgap0 : 0 < meanGap p q) (hgapn : meanGap p q < n) : p ≠ (fun _ => 1) := by
  intro hp
  subst p
  have hn0 : (0 : ℝ) < n := by positivity
  let b := (∑ i, q i) / n
  have hgap : meanGap (fun _ : Fin n => 1) q = n * (1-b) := by
    simp only [meanGap, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    dsimp [b]
    field_simp
  have hb0 : 0 < b := by rw [hgap] at hgapn; nlinarith
  have hb1 : b < 1 := by rw [hgap] at hgap0; nlinarith
  have hprod := product_le_mean_pow (by omega : 0 < n) q (fun i => (h.2.1 i).1)
  have hle : tailObjective (fun _ : Fin n => 1) (fun _ => b) ≤
      tailObjective (fun _ : Fin n => 1) q := by
    rw [tailObjective_one_left (by omega) (fun _ => ⟨hb0.le,hb1.le⟩),
      tailObjective_one_left (by omega) h.2.1]
    simpa only [prod_const, card_univ, Fintype.card_fin] using sub_le_sub_left hprod 1
  have hstrict := benchmark_lt_homogeneous_one_left (by omega : 2 ≤ n) hb0 hb1
  have hmin := hm.le_benchmark (by omega) hgap0 hgapn
  rw [hgap] at hmin
  linarith

/-- Reflection excludes an identically zero lower vector. -/
theorem IsGapMinimizer.lower_ne_zero {n : ℕ} (hn : 3 ≤ n) {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hgap0 : 0 < meanGap p q) (hgapn : meanGap p q < n) : q ≠ (fun _ => 0) := by
  have hh := hm.reflection.upper_ne_one hn (admissiblePair_reflection h)
    (by rwa [meanGap_reflection]) (by rwa [meanGap_reflection])
  intro hq
  apply hh
  simp [hq]

end PoissonBinomialComparison
