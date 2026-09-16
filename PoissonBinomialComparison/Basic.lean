import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Elementary Poisson--binomial objects

An outcome of the Bernoulli product on a finite coordinate set `s` is represented
by its set `A ⊆ s` of successful coordinates. Its weight is the product of the
success and failure parameters. The count `S_p` in the manuscript is thus `A.card`.
No measure-theoretic probability space is introduced.

`pbMass` is the manuscript's count mass, and `pbTail p k` is its upper tail at `k`.
The helpers with suffix `On` allow a coordinate to be deleted without relabelling
the remaining coordinates. All algebraic identities hold for arbitrary real
parameters; nonnegativity requires parameters in `[0, 1]`.

Counts and thresholds are natural numbers. The mass recurrence is stated at
`k + 1`, with a separate zero-count lemma, avoiding truncated subtraction at zero.
The tail at zero is one, including for the empty coordinate set.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Weight of the Bernoulli outcome with successes `A`, for `A ⊆ s`. -/
def bernoulliWeight (p : ι → ℝ) (s A : Finset ι) : ℝ :=
  (∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)

/-- Count mass on a finite coordinate set, in the manuscript's subset-sum form. -/
def pbMassOn (p : ι → ℝ) (s : Finset ι) (k : ℕ) : ℝ :=
  ∑ A ∈ s.powersetCard k, bernoulliWeight p s A

/-- Upper tail on a finite coordinate set, summing outcomes with at least `k` successes. -/
def pbTailOn (p : ι → ℝ) (s : Finset ι) (k : ℕ) : ℝ :=
  ∑ A ∈ s.powerset, if k ≤ A.card then bernoulliWeight p s A else 0

/-- The Poisson--binomial count mass for `n` parameters. -/
def pbMass {n : ℕ} (p : Fin n → ℝ) (k : ℕ) : ℝ :=
  pbMassOn p univ k

/-- The upper tail `P(S_p ≥ k)`, represented as a finite algebraic sum. -/
def pbTail {n : ℕ} (p : Fin n → ℝ) (k : ℕ) : ℝ :=
  pbTailOn p univ k

/-- The total mean gap `Δ` from the manuscript. -/
def meanGap {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  (∑ i, p i) - ∑ i, q i

/-- The count-tail difference `D_k(p,q)` from the manuscript. -/
def tailDiff {n : ℕ} (p q : Fin n → ℝ) (k : ℕ) : ℝ :=
  pbTail p k - pbTail q k

/-- Cardinality filtering gives an equivalent sum over the entire powerset. -/
theorem pbMassOn_eq_sum_powerset (p : ι → ℝ) (s : Finset ι) (k : ℕ) :
    pbMassOn p s k =
      ∑ A ∈ s.powerset, if A.card = k then bernoulliWeight p s A else 0 := by
  simp only [pbMassOn, powersetCard_eq_filter, sum_filter]

theorem bernoulliWeight_nonneg {p : ι → ℝ} {s A : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (hA : A ⊆ s) :
    0 ≤ bernoulliWeight p s A := by
  apply mul_nonneg
  · exact prod_nonneg fun i hi ↦ (hp i (hA hi)).1
  · exact prod_nonneg fun i hi ↦ sub_nonneg.mpr (hp i (mem_sdiff.mp hi).1).2

theorem pbMassOn_nonneg {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (k : ℕ) :
    0 ≤ pbMassOn p s k := by
  exact sum_nonneg fun A hA ↦ bernoulliWeight_nonneg hp (mem_powersetCard.mp hA).1

/-- Normalization of the algebraic product Bernoulli law. -/
theorem sum_bernoulliWeight (p : ι → ℝ) (s : Finset ι) :
    ∑ A ∈ s.powerset, bernoulliWeight p s A = 1 := by
  simpa [bernoulliWeight] using (prod_add p (fun i ↦ 1 - p i) s).symm

/-- Grouping outcomes by their number of successes preserves total mass. -/
theorem sum_pbMassOn (p : ι → ℝ) (s : Finset ι) :
    ∑ k ∈ range (s.card + 1), pbMassOn p s k = 1 := by
  simp only [pbMassOn]
  rw [← sum_powerset s (bernoulliWeight p s)]
  exact sum_bernoulliWeight p s

/-- The outcome-based upper tail equals the sum of count masses on `[k, #s]`. -/
theorem pbTailOn_eq_sum_mass (p : ι → ℝ) (s : Finset ι) (k : ℕ) :
    pbTailOn p s k = ∑ j ∈ Icc k s.card, pbMassOn p s j := by
  have hinterval : Icc k s.card = (range (s.card + 1)).filter (k ≤ ·) := by
    ext j
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  rw [pbTailOn, sum_powerset, hinterval, sum_filter]
  apply sum_congr rfl
  intro j hj
  by_cases hkj : k ≤ j
  · rw [ite_eq_left hkj]
    apply sum_congr rfl
    intro A hA
    simp [(mem_powersetCard.mp hA).2, hkj]
  · rw [ite_eq_right hkj]
    apply sum_eq_zero
    intro A hA
    simp [(mem_powersetCard.mp hA).2, hkj]

@[simp] theorem pbMassOn_zero (p : ι → ℝ) (s : Finset ι) :
    pbMassOn p s 0 = ∏ i ∈ s, (1 - p i) := by
  simp [pbMassOn, bernoulliWeight]

theorem pbMassOn_eq_zero_of_card_lt (p : ι → ℝ) {s : Finset ι} {k : ℕ}
    (hk : s.card < k) : pbMassOn p s k = 0 := by
  simp [pbMassOn, powersetCard_eq_empty.mpr hk]

@[simp] theorem pbTailOn_zero (p : ι → ℝ) (s : Finset ι) :
    pbTailOn p s 0 = 1 := by
  simpa [pbTailOn] using sum_bernoulliWeight p s

theorem pbTailOn_eq_zero_of_card_lt (p : ι → ℝ) {s : Finset ι} {k : ℕ}
    (hk : s.card < k) : pbTailOn p s k = 0 := by
  rw [pbTailOn_eq_sum_mass, Icc_eq_empty_of_lt hk, sum_empty]

private theorem bernoulliWeight_insert_failure (p : ι → ℝ) {s A : Finset ι}
    {i : ι} (hi : i ∉ s) (hA : A ⊆ s) :
    bernoulliWeight p (insert i s) A = (1 - p i) * bernoulliWeight p s A := by
  have hiA : i ∉ A := fun h ↦ hi (hA h)
  simp [bernoulliWeight, insert_sdiff_of_notMem s hiA, prod_insert,
    hi, mul_left_comm]

private theorem bernoulliWeight_insert_success (p : ι → ℝ) {s A : Finset ι}
    {i : ι} (hi : i ∉ s) (hA : A ⊆ s) :
    bernoulliWeight p (insert i s) (insert i A) = p i * bernoulliWeight p s A := by
  have hiA : i ∉ A := fun h ↦ hi (hA h)
  simp [bernoulliWeight, insert_sdiff_insert, sdiff_insert_of_notMem hi,
    prod_insert, hiA, mul_assoc]

/-- Splitting outcomes according to the added coordinate gives the mass recurrence. -/
theorem pbMassOn_insert_succ (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (k : ℕ) :
    pbMassOn p (insert i s) (k + 1) =
      (1 - p i) * pbMassOn p s (k + 1) + p i * pbMassOn p s k := by
  simp only [pbMassOn_eq_sum_powerset, sum_powerset_insert hi, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro A hA
    rw [bernoulliWeight_insert_failure p hi (mem_powerset.mp hA)]
    simp only [mul_ite, mul_zero]
  · apply sum_congr rfl
    intro A hA
    have hAs := mem_powerset.mp hA
    have hiA : i ∉ A := fun h ↦ hi (hAs h)
    rw [card_insert_of_notMem hiA, bernoulliWeight_insert_success p hi hAs]
    simp only [Nat.add_right_cancel_iff, mul_ite, mul_zero]

/-- The zero-count case of the mass recurrence. -/
theorem pbMassOn_insert_zero (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) :
    pbMassOn p (insert i s) 0 = (1 - p i) * pbMassOn p s 0 := by
  simp [prod_insert, hi]

/-- Splitting outcomes according to the added coordinate gives the tail recurrence. -/
theorem pbTailOn_insert_succ (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (k : ℕ) :
    pbTailOn p (insert i s) (k + 1) =
      (1 - p i) * pbTailOn p s (k + 1) + p i * pbTailOn p s k := by
  simp only [pbTailOn, sum_powerset_insert hi, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro A hA
    rw [bernoulliWeight_insert_failure p hi (mem_powerset.mp hA)]
    simp only [mul_ite, mul_zero]
  · apply sum_congr rfl
    intro A hA
    have hAs := mem_powerset.mp hA
    have hiA : i ∉ A := fun h ↦ hi (hAs h)
    rw [card_insert_of_notMem hiA, bernoulliWeight_insert_success p hi hAs]
    simp only [Nat.add_le_add_iff_right, mul_ite, mul_zero]

variable {n : ℕ}

/-- Explicit subset formula matching the manuscript, with complement inside `Fin n`. -/
theorem pbMass_eq_sum_subsets (p : Fin n → ℝ) (k : ℕ) :
    pbMass p k = ∑ A ∈ (univ : Finset (Fin n)).powersetCard k,
      (∏ i ∈ A, p i) * ∏ i ∈ univ \ A, (1 - p i) := rfl

theorem pbMass_nonneg {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (k : ℕ) : 0 ≤ pbMass p k :=
  pbMassOn_nonneg (fun i _ ↦ hp i) k

theorem sum_pbMass (p : Fin n → ℝ) : ∑ k ∈ range (n + 1), pbMass p k = 1 := by
  simpa [pbMass] using sum_pbMassOn p univ

theorem pbTail_eq_sum_mass (p : Fin n → ℝ) (k : ℕ) :
    pbTail p k = ∑ j ∈ Icc k n, pbMass p j := by
  simpa [pbTail, pbMass] using pbTailOn_eq_sum_mass p univ k

@[simp] theorem pbMass_zero (p : Fin n → ℝ) : pbMass p 0 = ∏ i, (1 - p i) :=
  pbMassOn_zero p univ

theorem pbMass_eq_zero_of_lt (p : Fin n → ℝ) {k : ℕ} (hk : n < k) :
    pbMass p k = 0 :=
  pbMassOn_eq_zero_of_card_lt p (by simpa using hk)

@[simp] theorem pbTail_zero (p : Fin n → ℝ) : pbTail p 0 = 1 :=
  pbTailOn_zero p univ

theorem pbTail_eq_zero_of_lt (p : Fin n → ℝ) {k : ℕ} (hk : n < k) :
    pbTail p k = 0 :=
  pbTailOn_eq_zero_of_card_lt p (by simpa using hk)

/-- Delete any coordinate, keeping the original labels on the others. -/
theorem pbMass_delete_succ (p : Fin n → ℝ) (i : Fin n) (k : ℕ) :
    pbMass p (k + 1) =
      (1 - p i) * pbMassOn p (univ.erase i) (k + 1) +
        p i * pbMassOn p (univ.erase i) k := by
  simpa [pbMass] using pbMassOn_insert_succ p (notMem_erase i univ) k

theorem pbMass_delete_zero (p : Fin n → ℝ) (i : Fin n) :
    pbMass p 0 = (1 - p i) * pbMassOn p (univ.erase i) 0 := by
  simpa [pbMass] using pbMassOn_insert_zero p (notMem_erase i univ)

theorem pbTail_delete_succ (p : Fin n → ℝ) (i : Fin n) (k : ℕ) :
    pbTail p (k + 1) =
      (1 - p i) * pbTailOn p (univ.erase i) (k + 1) +
        p i * pbTailOn p (univ.erase i) k := by
  simpa [pbTail] using pbTailOn_insert_succ p (notMem_erase i univ) k

theorem meanGap_eq_sum (p q : Fin n → ℝ) : meanGap p q = ∑ i, (p i - q i) := by
  exact (sum_sub_distrib p q).symm

theorem tailDiff_eq_sum_mass (p q : Fin n → ℝ) (k : ℕ) :
    tailDiff p q k = ∑ j ∈ Icc k n, (pbMass p j - pbMass q j) := by
  simp only [tailDiff, pbTail_eq_sum_mass, sum_sub_distrib]

end

end PoissonBinomialComparison
