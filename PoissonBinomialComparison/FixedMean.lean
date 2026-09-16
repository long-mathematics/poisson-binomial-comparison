import PoissonBinomialComparison.Compactness
import PoissonBinomialComparison.RandomizedThreshold

/-!
# Fixed-mean extremizers

Compactness allows a secondary minimization of the sum of squared parameters.
The count objective is a symmetric quadratic in every pair of coordinates.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ}

/-- Valid parameter vectors with a prescribed mean. -/
def parameterSlice (n : ℕ) (μ : ℝ) : Set (Fin n → ℝ) :=
  {p | ValidParameters p ∧ ∑ i, p i = μ}

/-- The secondary objective in the fixed-mean averaging argument. -/
def squareSum (p : Fin n → ℝ) : ℝ := ∑ i, (p i) ^ 2

@[fun_prop] theorem continuous_squareSum : Continuous (squareSum (n := n)) := by
  unfold squareSum
  fun_prop

theorem isCompact_parameterSlice (μ : ℝ) : IsCompact (parameterSlice n μ) := by
  have heq : parameterSlice n μ = Set.Icc (0 : Fin n → ℝ) 1 ∩ {p | ∑ i, p i = μ} := by
    ext p
    simp only [parameterSlice, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc,
      ValidParameters, Pi.le_def, Pi.zero_apply, Pi.one_apply]
    simp only [forall_and]
  rw [heq]
  exact isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)

theorem parameterSlice_nonempty (μ : ℝ) (h0 : 0 ≤ μ) (hn : μ ≤ n) :
    (parameterSlice n μ).Nonempty := by
  obtain ⟨⟨p, q⟩, h, hg⟩ := feasiblePairs_nonempty μ h0 hn
  refine ⟨fun i ↦ p i - q i, ?_, ?_⟩
  · intro i
    have hi := (admissiblePair_iff p q).mp h i
    exact ⟨sub_nonneg.mpr hi.2.1, by linarith⟩
  · rw [← meanGap_eq_sum]
    exact hg

/-- A primary continuous objective on a compact set admits a minimizer which
also minimizes any continuous secondary objective among the primary minimizers. -/
theorem exists_lexicographic_minimizer {α : Type*} [TopologicalSpace α]
    {s : Set α} (hs : IsCompact s) (hne : s.Nonempty) (f g : α → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    ∃ x ∈ s, (∀ y ∈ s, f x ≤ f y) ∧
      ∀ y ∈ s, f y = f x → g x ≤ g y := by
  obtain ⟨x, hx, hmin⟩ := hs.exists_isMinOn hne hf.continuousOn
  have hc : IsCompact (s ∩ {y | f y = f x}) :=
    hs.inter_right (isClosed_eq hf continuous_const)
  obtain ⟨z, hz, hzmin⟩ := hc.exists_isMinOn ⟨x, hx, rfl⟩ hg.continuousOn
  refine ⟨z, hz.1, ?_, ?_⟩
  · intro y hy
    rw [hz.2]
    exact (isMinOn_iff.mp hmin) y hy
  · intro y hy he
    exact (isMinOn_iff.mp hzmin) y ⟨hy, he.trans hz.2⟩

/-- The compact extremizer selected in the manuscript's integer-mean reduction.
This existence statement holds for every feasible real mean. -/
theorem exists_mass_minimizer_minimal_squareSum (μ : ℝ) (h0 : 0 ≤ μ)
    (hn : μ ≤ n) (k : ℕ) :
    ∃ p ∈ parameterSlice n μ,
      (∀ q ∈ parameterSlice n μ, pbMass p k ≤ pbMass q k) ∧
      ∀ q ∈ parameterSlice n μ, pbMass q k = pbMass p k → squareSum p ≤ squareSum q :=
  exists_lexicographic_minimizer (isCompact_parameterSlice μ)
    (parameterSlice_nonempty μ h0 hn) (fun p ↦ pbMass p k) squareSum
    (continuous_pbMass k) continuous_squareSum

/-- Every two-coordinate section has equal linear coefficients. -/
def SymmetricQuadraticUpdates (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ p (i j : Fin n), i ≠ j → ∃ A B C : ℝ, ∀ u v : ℝ,
    f (Function.update (Function.update p i u) j v) = A + B * (u + v) + C * u * v

/-- The mass objective has the exact symmetric pair polynomial used in averaging. -/
theorem pbMass_symmetricQuadraticUpdates (k : ℕ) :
    SymmetricQuadraticUpdates (fun p : Fin n → ℝ ↦ pbMass p k) := by
  intro p i j hij
  let s := (univ.erase i).erase j
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hs : insert i (insert j s) = univ := by
    ext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;> simp_all [s]
  refine ⟨randomizedTailOn p s 1 k - randomizedTailOn p s 0 k,
    randomizedSlopeOn p s 1 k - randomizedSlopeOn p s 0 k,
    randomizedCoefficientOn p s 1 k - randomizedCoefficientOn p s 0 k, ?_⟩
  intro u v
  dsimp only
  rw [← pbTail_sub_succ]
  have he (x : Fin n → ℝ) : pbTail x k - pbTail x (k + 1) =
      randomizedTailOn x univ 1 k - randomizedTailOn x univ 0 k := by
    simp [randomizedTailOn, pbTail]
  rw [he, ← hs, randomizedTailOn_update_update p hi hj hij,
    randomizedTailOn_update_update p hi hj hij]
  ring

/-- Updating one coordinate changes a separable sum by its exact local increment. -/
theorem sum_map_update (F : ℝ → ℝ) (p : Fin n → ℝ) (i : Fin n) (u : ℝ) :
    (∑ l, F (Function.update p i u l)) = ∑ l, F (p l) + F u - F (p i) := by
  have he : (fun l ↦ F (Function.update p i u l)) =
      Function.update (fun l ↦ F (p l)) i (F u) := Function.comp_update F p i u
  rw [he, sum_update_of_mem (mem_univ i)]
  have h := sum_erase_add univ (fun l ↦ F (p l)) (mem_univ i)
  rw [sdiff_singleton_eq_erase]
  linarith

theorem squareSum_update (p : Fin n → ℝ) (i : Fin n) (u : ℝ) :
    squareSum (Function.update p i u) = squareSum p + u ^ 2 - (p i) ^ 2 :=
  sum_map_update (fun x ↦ x ^ 2) p i u

/-- Pair transfers preserve the prescribed mean and preserve validity when the
new coordinates lie in the unit interval. -/
theorem update_pair_mem_parameterSlice {p : Fin n → ℝ} {μ : ℝ}
    (hp : p ∈ parameterSlice n μ) {i j : Fin n} (hij : i ≠ j)
    {u v : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (hsum : u + v = p i + p j) :
    Function.update (Function.update p i u) j v ∈ parameterSlice n μ := by
  constructor
  · intro l
    by_cases hlj : l = j
    · subst l
      simpa using hv
    · by_cases hli : l = i
      · subst l
        simpa [Function.update_of_ne hij] using hu
      · simpa [Function.update_of_ne hlj, Function.update_of_ne hli] using hp.1 l
  · change (∑ l, id (Function.update (Function.update p i u) j v l)) = μ
    rw [sum_map_update, sum_map_update]
    simp only [id_eq, Function.update_of_ne (Ne.symm hij)]
    rw [hp.2]
    linarith

private theorem no_distinct_ordered_interior {f : (Fin n → ℝ) → ℝ}
    (hf : SymmetricQuadraticUpdates f) {p : Fin n → ℝ} {μ : ℝ}
    (hp : p ∈ parameterSlice n μ)
    (hmin : ∀ q ∈ parameterSlice n μ, f p ≤ f q)
    (hsec : ∀ q ∈ parameterSlice n μ, f q = f p → squareSum p ≤ squareSum q)
    {i j : Fin n} (hij : i ≠ j) (hi : 0 < p i) (hj : p j < 1)
    (hlt : p i < p j) : False := by
  obtain ⟨A, B, C, hpoly⟩ := hf p i j hij
  have hbase : f p = A + B * (p i + p j) + C * p i * p j := by
    simpa only [Function.update_eq_self] using hpoly (p i) (p j)
  let a := (p i + p j) / 2
  have ha : 0 ≤ a ∧ a ≤ 1 := by dsimp [a]; constructor <;> linarith
  have hamean : a + a = p i + p j := by dsimp [a]; ring
  have hamem := update_pair_mem_parameterSlice hp hij ha ha hamean
  have havg := hmin _ hamem
  rw [hbase, hpoly] at havg
  have hsquare : 0 < (p i - p j) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hc0 : 0 ≤ C := by
    apply (mul_nonneg_iff_of_pos_right hsquare).mp
    dsimp [a] at havg
    nlinarith only [havg]
  let t := min (p i) (1 - p j)
  have ht : 0 < t := lt_min hi (by linarith)
  have hti : t ≤ p i := min_le_left _ _
  have htj : t ≤ 1 - p j := min_le_right _ _
  have hui : 0 ≤ p i - t ∧ p i - t ≤ 1 := ⟨by linarith, by linarith⟩
  have hvj : 0 ≤ p j + t ∧ p j + t ≤ 1 := ⟨by linarith, by linarith⟩
  have hspread := hmin _ (update_pair_mem_parameterSlice hp hij hui hvj (by ring))
  rw [hbase, hpoly] at hspread
  have hfac : 0 < t * (p j - p i + t) := mul_pos ht (by linarith)
  have hc1 : C ≤ 0 := by
    have hprod : C * (t * (p j - p i + t)) ≤ 0 := by nlinarith only [hspread]
    exact nonpos_of_mul_nonpos_left hprod hfac
  have hcz : C = 0 := le_antisymm hc1 hc0
  have heq : f (Function.update (Function.update p i a) j a) = f p := by
    rw [hpoly, hbase, hcz, hamean]
    ring
  have hs := hsec _ hamem heq
  rw [squareSum_update, squareSum_update, Function.update_of_ne (Ne.symm hij)] at hs
  dsimp [a] at hs
  nlinarith only [hs, hsquare]

/-- A minimizer selected by the square-sum tie breaker has equal strictly
interior coordinates. This is the manuscript's pair-averaging argument. -/
theorem interior_coordinates_eq_of_minimal_squareSum {f : (Fin n → ℝ) → ℝ}
    (hf : SymmetricQuadraticUpdates f) {p : Fin n → ℝ} {μ : ℝ}
    (hp : p ∈ parameterSlice n μ)
    (hmin : ∀ q ∈ parameterSlice n μ, f p ≤ f q)
    (hsec : ∀ q ∈ parameterSlice n μ, f q = f p → squareSum p ≤ squareSum q)
    (i j : Fin n) (hi : 0 < p i ∧ p i < 1) (hj : 0 < p j ∧ p j < 1) :
    p i = p j := by
  by_contra hne
  have hij : i ≠ j := fun he ↦ hne (congrArg p he)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact no_distinct_ordered_interior hf hp hmin hsec hij hi.1 hj.2 hlt
  · exact no_distinct_ordered_interior hf hp hmin hsec (Ne.symm hij) hj.1 hi.2 hgt

/-- Every feasible count-mass minimization admits an extremizer whose
nondeterministic coordinates are all equal. No integer-mean hypothesis is needed. -/
theorem exists_mass_minimizer_equal_interior (μ : ℝ) (h0 : 0 ≤ μ)
    (hn : μ ≤ n) (k : ℕ) :
    ∃ p ∈ parameterSlice n μ,
      (∀ q ∈ parameterSlice n μ, pbMass p k ≤ pbMass q k) ∧
      ∀ i j, (0 < p i ∧ p i < 1) → (0 < p j ∧ p j < 1) → p i = p j := by
  obtain ⟨p, hp, hmin, hsec⟩ := exists_mass_minimizer_minimal_squareSum μ h0 hn k
  exact ⟨p, hp, hmin, interior_coordinates_eq_of_minimal_squareSum
    (pbMass_symmetricQuadraticUpdates k) hp hmin hsec⟩

end

end PoissonBinomialComparison
