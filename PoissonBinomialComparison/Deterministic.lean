import PoissonBinomialComparison.HomogeneousBlock
import PoissonBinomialComparison.Homogeneous
import PoissonBinomialComparison.FixedMean

/-!
# Deterministic shifts and binomial decomposition

A vector whose interior parameters all agree is a deterministic shift plus a
homogeneous Bernoulli block. Both its mean and count law are identified exactly.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Empty-background homogeneous blocks are independent of the ambient index type. -/
theorem homogeneousBlockMass_empty_eq {κ : Type*} [DecidableEq κ]
    (p : ι → ℝ) (q : κ → ℝ) (M : ℕ) (t : ℝ) (k : ℤ) :
    homogeneousBlockMass p ∅ M t k = homogeneousBlockMass q ∅ M t k := by
  induction M generalizing k with
  | zero => simp
  | succ M ih => simp only [homogeneousBlockMass_succ, ih]

/-- An empty-background block is exactly a homogeneous subset-sum law. -/
theorem homogeneousBlockMass_empty_eq_pbMassInt (p : ι → ℝ) (M : ℕ) (t : ℝ) (k : ℤ) :
    homogeneousBlockMass p ∅ M t k =
      pbMassIntOn (fun _ : Fin M ↦ t) univ k := by
  rw [homogeneousBlockMass_empty_eq p (fun _ : Fin M ↦ t)]
  simpa using homogeneousBlockMass_eq_union (fun _ : Fin M ↦ t) ∅ univ
    (by simp) t (by simp) k

/-- Exact decomposition when every parameter is zero, one, or a common value.
The counts include deterministic degeneracies and the empty coordinate set. -/
theorem exists_deterministic_binomial_decomposition (p : ι → ℝ) (s : Finset ι)
    (t : ℝ) (hp : ∀ i ∈ s, p i = 0 ∨ p i = 1 ∨ p i = t) :
    ∃ J M : ℕ, J + M ≤ s.card ∧
      (∑ i ∈ s, p i) = (J : ℝ) + M * t ∧
      ∀ k : ℤ, pbMassIntOn p s k =
        homogeneousBlockMass (fun _ : Unit ↦ (0 : ℝ)) ∅ M t (k - J) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, 0, by simp, by simp, ?_⟩
    intro k
    simp
  | @insert i s hi ih =>
    obtain ⟨J, M, hcard, hsum, hmass⟩ := ih (fun j hj ↦ hp j (mem_insert_of_mem hj))
    rcases hp i (mem_insert_self i s) with hz | ho | ht
    · refine ⟨J, M, ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem hi]
        omega
      · rw [sum_insert hi, hz, zero_add, hsum]
      · intro k
        rw [pbMassIntOn_insert p hi, hz]
        simpa using hmass k
    · refine ⟨J + 1, M, ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem hi]
        omega
      · rw [sum_insert hi, ho, hsum, Nat.cast_add, Nat.cast_one]
        ring
      · intro k
        rw [pbMassIntOn_insert p hi, ho]
        simp only [sub_self, zero_mul, one_mul, zero_add, hmass]
        congr 1
        omega
    · refine ⟨J, M + 1, ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem hi]
        omega
      · rw [sum_insert hi, ht, hsum, Nat.cast_add, Nat.cast_one]
        ring
      · intro k
        rw [pbMassIntOn_insert p hi, ht, hmass, hmass, homogeneousBlockMass_succ]
        rw [show k - 1 - (J : ℤ) = k - J - 1 by omega]

variable {n : ℕ}

/-- Equal interior coordinates force the exact deterministic-plus-binomial form. -/
theorem equal_interior_binomial_decomposition {p : Fin n → ℝ}
    (hp : ValidParameters p)
    (heq : ∀ i j, (0 < p i ∧ p i < 1) → (0 < p j ∧ p j < 1) → p i = p j) :
    ∃ (t : ℝ) (J M : ℕ), 0 ≤ t ∧ t ≤ 1 ∧ J + M ≤ n ∧
      (∑ i, p i) = (J : ℝ) + M * t ∧
      ∀ k : ℤ, pbMassIntOn p univ k = pbMassIntOn (fun _ : Fin M ↦ t) univ (k - J) := by
  have hex : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧ ∀ i, p i = 0 ∨ p i = 1 ∨ p i = t := by
    by_cases h : ∃ i, 0 < p i ∧ p i < 1
    · obtain ⟨i, hi⟩ := h
      refine ⟨p i, hp i, ?_⟩
      intro j
      by_cases hj0 : p j = 0
      · exact Or.inl hj0
      by_cases hj1 : p j = 1
      · exact Or.inr (Or.inl hj1)
      exact Or.inr (Or.inr (heq j i
        ⟨lt_of_le_of_ne (hp j).1 (Ne.symm hj0), lt_of_le_of_ne (hp j).2 hj1⟩ hi))
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      intro i
      by_cases hi0 : p i = 0
      · exact Or.inl hi0
      right
      left
      by_contra hi1
      exact h ⟨i, lt_of_le_of_ne (hp i).1 (Ne.symm hi0), lt_of_le_of_ne (hp i).2 hi1⟩
  obtain ⟨t, ht, hvalues⟩ := hex
  obtain ⟨J, M, hcard, hsum, hmass⟩ :=
    exists_deterministic_binomial_decomposition p univ t (fun i _ ↦ hvalues i)
  refine ⟨t, J, M, ht.1, ht.2, ?_, hsum, ?_⟩
  · simpa using hcard
  · intro k
    rw [hmass, homogeneousBlockMass_empty_eq_pbMassInt]

/-- At integer mean an equal-interior law has exactly a binomial integer-mean
mass after removing its deterministic shift. -/
theorem integer_mean_binomial_decomposition {p : Fin n → ℝ}
    (hp : ValidParameters p) (k : ℕ) (hmean : (∑ i, p i) = k)
    (heq : ∀ i j, (0 < p i ∧ p i < 1) → (0 < p j ∧ p j < 1) → p i = p j) :
    ∃ M ℓ : ℕ, M ≤ n ∧ ℓ ≤ M ∧
      pbMass p k = pbMass (fun _ : Fin M ↦ (ℓ : ℝ) / M) ℓ := by
  obtain ⟨t, J, M, ht0, ht1, hcard, hsum, hmass⟩ := equal_interior_binomial_decomposition hp heq
  have hm0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hJk : J ≤ k := by
    have hr : (J : ℝ) ≤ k := by rw [hmean] at hsum; nlinarith
    exact_mod_cast hr
  have hkJM : k ≤ J + M := by
    have hr : (k : ℝ) ≤ J + M := by rw [hmean] at hsum; nlinarith
    exact_mod_cast hr
  let ℓ := k - J
  have hℓ : ℓ ≤ M := by dsimp [ℓ]; omega
  have hcast : (k : ℤ) - J = (ℓ : ℤ) := by dsimp [ℓ]; omega
  have hmass' : pbMass p k = pbMass (fun _ : Fin M ↦ t) ℓ := by
    have h := hmass (k : ℤ)
    rw [hcast, pbMassIntOn_natCast, pbMassIntOn_natCast] at h
    exact h
  refine ⟨M, ℓ, by omega, hℓ, ?_⟩
  by_cases hM : M = 0
  · have hℓ0 : ℓ = 0 := by omega
    rw [hmass', hM, hℓ0]
    simp
  · have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM
    have ht : t = (ℓ : ℝ) / M := by
      apply (eq_div_iff hMr).mpr
      dsimp [ℓ]
      rw [Nat.cast_sub hJk]
      rw [hmean] at hsum
      linarith
    rw [hmass', ht]

/-- Every integer-mean mass is bounded below by an integer-mean binomial mass
in some dimension no larger than the original one. -/
theorem exists_binomial_mass_le_integer_mean_mass {p : Fin n → ℝ}
    (hp : ValidParameters p) (k : ℕ) (hmean : (∑ i, p i) = k) :
    ∃ M ℓ : ℕ, M ≤ n ∧ ℓ ≤ M ∧
      pbMass (fun _ : Fin M ↦ (ℓ : ℝ) / M) ℓ ≤ pbMass p k := by
  have hkn : (k : ℝ) ≤ n := by
    calc
      (k : ℝ) = ∑ i, p i := hmean.symm
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := sum_le_sum (fun i _ ↦ (hp i).2)
      _ = n := by simp
  obtain ⟨q, hq, hmin, heq⟩ := exists_mass_minimizer_equal_interior
    (k : ℝ) (Nat.cast_nonneg k) hkn k
  obtain ⟨M, ℓ, hM, hℓ, hmass⟩ := integer_mean_binomial_decomposition hq.1 k hq.2 heq
  refine ⟨M, ℓ, hM, hℓ, ?_⟩
  rw [← hmass]
  exact hmin p ⟨hp, hmean⟩

end

end PoissonBinomialComparison
