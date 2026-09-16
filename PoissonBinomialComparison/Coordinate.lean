import PoissonBinomialComparison.Tail

/-!
# Coordinate identities for Bernoulli sums

All identities are algebraic and hold for arbitrary real parameters. Changing
one coordinate changes an upper tail by the parameter increment times the
corresponding mass of the deleted-coordinate sum. Nonnegativity of that mass
then gives monotonicity for valid Bernoulli parameters.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- An outcome weight depends only on the parameters in its coordinate set. -/
theorem bernoulliWeight_congr {p q : ι → ℝ} {s A : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (hA : A ⊆ s) :
    bernoulliWeight p s A = bernoulliWeight q s A := by
  unfold bernoulliWeight
  congr 1
  · exact prod_congr rfl fun i hi ↦ h i (hA hi)
  · exact prod_congr rfl fun i hi ↦ congrArg (1 - ·) (h i (mem_sdiff.mp hi).1)

/-- A count mass depends only on the parameters in its coordinate set. -/
theorem pbMassOn_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (k : ℕ) :
    pbMassOn p s k = pbMassOn q s k := by
  exact sum_congr rfl fun A hA ↦ bernoulliWeight_congr h (mem_powersetCard.mp hA).1

/-- An upper tail depends only on the parameters in its coordinate set. -/
theorem pbTailOn_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (k : ℕ) :
    pbTailOn p s k = pbTailOn q s k := by
  unfold pbTailOn
  apply sum_congr rfl
  intro A hA
  rw [bernoulliWeight_congr h (mem_powerset.mp hA)]

/-- The difference of adjacent upper tails is exactly the intervening count mass. -/
theorem pbTailOn_sub_succ (p : ι → ℝ) (s : Finset ι) (k : ℕ) :
    pbTailOn p s k - pbTailOn p s (k + 1) = pbMassOn p s k := by
  rw [pbTailOn, pbTailOn, ← sum_sub_distrib, pbMassOn_eq_sum_powerset]
  apply sum_congr rfl
  intro A _
  by_cases h : A.card = k
  · simp [h]
  · by_cases hk : k ≤ A.card
    · have hk' : k + 1 ≤ A.card := by omega
      simp [h, hk, hk']
    · have hk' : ¬k + 1 ≤ A.card := by omega
      simp [h, hk, hk']

/-- Updating a parameter outside the coordinate set leaves its count mass unchanged. -/
theorem pbMassOn_update_of_notMem (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (a : ℝ) (k : ℕ) :
    pbMassOn (Function.update p i a) s k = pbMassOn p s k := by
  apply pbMassOn_congr
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  exact Function.update_of_ne hji a p

/-- Updating a parameter outside the coordinate set leaves its upper tail unchanged. -/
theorem pbTailOn_update_of_notMem (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (a : ℝ) (k : ℕ) :
    pbTailOn (Function.update p i a) s k = pbTailOn p s k := by
  apply pbTailOn_congr
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  exact Function.update_of_ne hji a p

/-- The affine upper-tail coefficient is the count mass after deleting the coordinate. -/
theorem pbTailOn_update_sub (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (a b : ℝ) (k : ℕ) :
    pbTailOn (Function.update p i b) (insert i s) (k + 1) -
      pbTailOn (Function.update p i a) (insert i s) (k + 1) =
        (b - a) * pbMassOn p s k := by
  rw [pbTailOn_insert_succ _ hi, pbTailOn_insert_succ _ hi]
  simp only [Function.update_self, pbTailOn_update_of_notMem p hi]
  rw [← pbTailOn_sub_succ p s k]
  ring

/-- Increasing a coordinate increases every positive-threshold tail, provided the
remaining coordinates are valid Bernoulli parameters. -/
theorem pbTailOn_update_mono (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1)
    {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    pbTailOn (Function.update p i a) (insert i s) (k + 1) ≤
      pbTailOn (Function.update p i b) (insert i s) (k + 1) := by
  apply sub_nonneg.mp
  rw [pbTailOn_update_sub p hi]
  exact mul_nonneg (sub_nonneg.mpr hab) (pbMassOn_nonneg hp k)

/-- Coordinatewise increasing valid Bernoulli parameters increases every tail. -/
theorem pbTailOn_mono {p q : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, p i ≤ q i) (k : ℕ) :
    pbTailOn p s k ≤ pbTailOn q s k := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp [pbTailOn, bernoulliWeight]
  | @insert i s hi ih =>
    have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 :=
      fun j hj ↦ hp j (mem_insert_of_mem hj)
    have hqs : ∀ j ∈ s, 0 ≤ q j ∧ q j ≤ 1 :=
      fun j hj ↦ hq j (mem_insert_of_mem hj)
    have hpqs : ∀ j ∈ s, p j ≤ q j :=
      fun j hj ↦ hpq j (mem_insert_of_mem hj)
    cases k with
    | zero => simp
    | succ k =>
      rw [pbTailOn_insert_succ _ hi, pbTailOn_insert_succ _ hi]
      calc
        (1 - p i) * pbTailOn p s (k + 1) + p i * pbTailOn p s k ≤
            (1 - p i) * pbTailOn q s (k + 1) + p i * pbTailOn q s k :=
          add_le_add
            (mul_le_mul_of_nonneg_left (ih hps hqs hpqs (k + 1))
              (sub_nonneg.mpr (hp i (mem_insert_self i s)).2))
            (mul_le_mul_of_nonneg_left (ih hps hqs hpqs k)
              (hp i (mem_insert_self i s)).1)
        _ ≤ (1 - q i) * pbTailOn q s (k + 1) + q i * pbTailOn q s k := by
          apply sub_nonneg.mp
          have heq :
              (1 - q i) * pbTailOn q s (k + 1) + q i * pbTailOn q s k -
                ((1 - p i) * pbTailOn q s (k + 1) + p i * pbTailOn q s k) =
                  (q i - p i) * pbMassOn q s k := by
            rw [← pbTailOn_sub_succ q s k]
            ring
          rw [heq]
          exact mul_nonneg (sub_nonneg.mpr (hpq i (mem_insert_self i s)))
            (pbMassOn_nonneg hqs k)

variable {n : ℕ}

/-- Manuscript-facing adjacent-tail identity. -/
theorem pbTail_sub_succ (p : Fin n → ℝ) (k : ℕ) :
    pbTail p k - pbTail p (k + 1) = pbMass p k :=
  pbTailOn_sub_succ p univ k

/-- Exact one-coordinate change of a Poisson--binomial upper tail. -/
theorem pbTail_update_sub (p : Fin n → ℝ) (i : Fin n) (a b : ℝ) (k : ℕ) :
    pbTail (Function.update p i b) (k + 1) -
      pbTail (Function.update p i a) (k + 1) =
        (b - a) * pbMassOn p (univ.erase i) k := by
  simpa [pbTail] using pbTailOn_update_sub p (notMem_erase i univ) a b k

/-- Upper tails are monotone in any single Bernoulli parameter. -/
theorem pbTail_update_mono (p : Fin n → ℝ) (hp : ValidParameters p)
    (i : Fin n) {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    pbTail (Function.update p i a) k ≤ pbTail (Function.update p i b) k := by
  cases k with
  | zero => simp
  | succ k =>
    simpa [pbTail] using
      pbTailOn_update_mono p (notMem_erase i univ) (fun j _ ↦ hp j) hab k

/-- Poisson--binomial upper tails preserve coordinatewise parameter order. -/
theorem pbTail_mono {p q : Fin n → ℝ} (hp : ValidParameters p)
    (hq : ValidParameters q) (hpq : p ≤ q) (k : ℕ) :
    pbTail p k ≤ pbTail q k :=
  pbTailOn_mono univ (fun i _ ↦ hp i) (fun i _ ↦ hq i) (fun i _ ↦ hpq i) k

/-- Every manuscript tail difference is nonnegative for an admissible pair. -/
theorem tailDiff_nonneg {p q : Fin n → ℝ} (h : AdmissiblePair p q) (k : ℕ) :
    0 ≤ tailDiff p q k :=
  sub_nonneg.mpr (pbTail_mono h.2.1 h.1 h.2.2 k)

end

end PoissonBinomialComparison
