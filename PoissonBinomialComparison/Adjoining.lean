import PoissonBinomialComparison.LogConcavity

/-!
# Adjoining Bernoulli variables on the increasing side of a count mass

If the mass at `k` is positive and at least the mass at `k - 1`, adjoining
Bernoulli variables cannot increase the mass at `k`. A stronger prefix-order
invariant handles deterministic parameters and disappearance of the mass.
This module proves finite algebraic statements, not analytic derivative claims.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

/-- A positive mass and an increasing adjacent pair force the entire preceding
mass sequence to be nondecreasing. -/
theorem MassCrossInequalities.prefix_order {f : ℤ → ℝ}
    (hc : MassCrossInequalities f) (hf : ∀ j, 0 ≤ f j) {k : ℤ}
    (hk : 0 < f k) (hadj : f (k - 1) ≤ f k) :
    ∀ j ≤ k, f (j - 1) ≤ f j := by
  intro j hj
  by_cases heq : j = k
  · simpa [heq] using hadj
  have hcross := hc j (k - 1) (by omega)
  simp only [show k - 1 + 1 = k by omega] at hcross
  have hmul := mul_le_mul_of_nonneg_left hadj (hf j)
  exact (mul_le_mul_iff_left₀ hk).mp (hcross.trans hmul)

private theorem prefix_order_le {f : ℤ → ℝ} {k j : ℤ}
    (h : ∀ l ≤ k, f (l - 1) ≤ f l) (hj : j ≤ k) : f j ≤ f k := by
  by_cases heq : j = k
  · simp [heq]
  have hstep : f j ≤ f (j + 1) := by simpa using h (j + 1) (by omega)
  exact hstep.trans (prefix_order_le h (j := j + 1) (by omega))
termination_by (k - j).toNat
decreasing_by omega

variable {ι : Type*} [DecidableEq ι]

/-- A single addition cannot increase a mass whose preceding mass is no larger. -/
theorem pbMassIntOn_insert_le {p : ι → ℝ} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hpi : 0 ≤ p i) (k : ℤ)
    (hadj : pbMassIntOn p s (k - 1) ≤ pbMassIntOn p s k) :
    pbMassIntOn p (insert i s) k ≤ pbMassIntOn p s k := by
  rw [pbMassIntOn_insert p hi]
  have h := mul_le_mul_of_nonneg_left hadj hpi
  linarith

/-- A positive addition strictly decreases a strictly increasing adjacent pair. -/
theorem pbMassIntOn_insert_lt {p : ι → ℝ} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hpi : 0 < p i) (k : ℤ)
    (hadj : pbMassIntOn p s (k - 1) < pbMassIntOn p s k) :
    pbMassIntOn p (insert i s) k < pbMassIntOn p s k := by
  rw [pbMassIntOn_insert p hi]
  have h := mul_lt_mul_of_pos_left hadj hpi
  linarith

/-- Convolution preserves the complete preceding-order invariant, even when the
mass at the target count becomes zero. -/
theorem pbMassIntOn_insert_prefix_order {p : ι → ℝ} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hpi : 0 ≤ p i ∧ p i ≤ 1) (k : ℤ)
    (hprefix : ∀ j ≤ k, pbMassIntOn p s (j - 1) ≤ pbMassIntOn p s j) :
    ∀ j ≤ k, pbMassIntOn p (insert i s) (j - 1) ≤ pbMassIntOn p (insert i s) j := by
  intro j hj
  rw [pbMassIntOn_insert p hi, pbMassIntOn_insert p hi]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hprefix j hj) (sub_nonneg.mpr hpi.2))
    (mul_le_mul_of_nonneg_left (hprefix (j - 1) (by omega)) hpi.1)

/-- The adjoining rule preserves adjacent order under its positive-mass hypothesis. -/
theorem pbMassIntOn_insert_adjacent_le {p : ι → ℝ} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1)
    (hpi : 0 ≤ p i ∧ p i ≤ 1) (k : ℤ)
    (hk : 0 < pbMassIntOn p s k)
    (hadj : pbMassIntOn p s (k - 1) ≤ pbMassIntOn p s k) :
    pbMassIntOn p (insert i s) (k - 1) ≤ pbMassIntOn p (insert i s) k := by
  exact pbMassIntOn_insert_prefix_order hi hpi k
    ((pbMassIntOn_cross s hp).prefix_order (pbMassIntOn_nonneg hp) hk hadj) k le_rfl

/-- An adjacent tie leaves the target mass unchanged after one addition. -/
theorem pbMassIntOn_insert_eq_of_tie {p : ι → ℝ} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (k : ℤ)
    (htie : pbMassIntOn p s (k - 1) = pbMassIntOn p s k) :
    pbMassIntOn p (insert i s) k = pbMassIntOn p s k := by
  rw [pbMassIntOn_insert p hi, htie]
  ring

/-- A positive addition turns a positive adjacent tie into a strict inequality. -/
theorem pbMassIntOn_insert_adjacent_lt_of_tie {p : ι → ℝ} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1) (hpi : 0 < p i)
    (k : ℤ) (hk : 0 < pbMassIntOn p s k)
    (htie : pbMassIntOn p s (k - 1) = pbMassIntOn p s k) :
    pbMassIntOn p (insert i s) (k - 1) < pbMassIntOn p (insert i s) k := by
  have hprev : 0 < pbMassIntOn p s (k - 1) := by rw [htie]; exact hk
  have hstrict := pbMassIntOn_strictLogConcavity s hp (k - 1) hprev
  simp only [show k - 1 + 1 = k by omega, htie, pow_two] at hstrict
  have hsmall : pbMassIntOn p s (k - 1 - 1) < pbMassIntOn p s k :=
    (mul_lt_mul_iff_left₀ hk).mp hstrict
  rw [pbMassIntOn_insert_eq_of_tie hi k htie, pbMassIntOn_insert p hi, htie]
  have hmul := mul_lt_mul_of_pos_left hsmall hpi
  linarith

/-- Two positive additions strictly decrease a positive tied mass, including
parameters equal to one. -/
theorem pbMassIntOn_insert_insert_lt_of_tie {p : ι → ℝ} {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j)
    (hp : ∀ l ∈ s, 0 ≤ p l ∧ p l ≤ 1) (hpi : 0 < p i) (hpj : 0 < p j)
    (k : ℤ) (hk : 0 < pbMassIntOn p s k)
    (htie : pbMassIntOn p s (k - 1) = pbMassIntOn p s k) :
    pbMassIntOn p (insert j (insert i s)) k < pbMassIntOn p s k := by
  have hj' : j ∉ insert i s := by simp [hj, Ne.symm hij]
  have hlt := pbMassIntOn_insert_lt hj' hpj k
    (pbMassIntOn_insert_adjacent_lt_of_tie hi hp hpi k hk htie)
  rwa [pbMassIntOn_insert_eq_of_tie hi k htie] at hlt

/-- Any finite collection of valid added parameters preserves the prefix-order
invariant and can only decrease the target mass. Already-present indices are harmless. -/
theorem pbMassIntOn_union_prefix_order {p : ι → ℝ} (s t : Finset ι)
    (hp : ∀ j ∈ s ∪ t, 0 ≤ p j ∧ p j ≤ 1) (k : ℤ)
    (hprefix : ∀ j ≤ k, pbMassIntOn p s (j - 1) ≤ pbMassIntOn p s j) :
    pbMassIntOn p (s ∪ t) k ≤ pbMassIntOn p s k ∧
      ∀ j ≤ k, pbMassIntOn p (s ∪ t) (j - 1) ≤ pbMassIntOn p (s ∪ t) j := by
  induction t using Finset.induction_on with
  | empty => simpa using And.intro (le_refl (pbMassIntOn p s k)) hprefix
  | @insert i t hi ih =>
    have hps : ∀ j ∈ s ∪ t, 0 ≤ p j ∧ p j ≤ 1 := by
      intro j hj
      exact hp j (by simp only [mem_union, mem_insert] at hj ⊢; tauto)
    obtain ⟨hle, hpre⟩ := ih hps
    have hpi : 0 ≤ p i ∧ p i ≤ 1 := hp i (by simp)
    rw [union_insert]
    by_cases him : i ∈ s ∪ t
    · rw [insert_eq_of_mem him]
      exact ⟨hle, hpre⟩
    · exact ⟨(pbMassIntOn_insert_le him hpi.1 k (hpre k le_rfl)).trans hle,
        pbMassIntOn_insert_prefix_order him hpi k hpre⟩

/-- The manuscript's finite adjoining rule, including arbitrary deterministic additions. -/
theorem pbMassIntOn_union_le_of_adjacent {p : ι → ℝ} (s t : Finset ι)
    (hp : ∀ j ∈ s ∪ t, 0 ≤ p j ∧ p j ≤ 1) (k : ℤ)
    (hk : 0 < pbMassIntOn p s k)
    (hadj : pbMassIntOn p s (k - 1) ≤ pbMassIntOn p s k) :
    pbMassIntOn p (s ∪ t) k ≤ pbMassIntOn p s k := by
  have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 := fun j hj ↦ hp j (mem_union_left t hj)
  exact (pbMassIntOn_union_prefix_order s t hp k
    ((pbMassIntOn_cross s hps).prefix_order (pbMassIntOn_nonneg hps) hk hadj)).1

/-- The strict improvement from two positive additions persists after any finite
collection of further valid additions, even if the target mass vanishes. -/
theorem pbMassIntOn_union_lt_of_two_positive_of_tie {p : ι → ℝ} (s t : Finset ι)
    {i j : ι} (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j)
    (hp : ∀ l ∈ insert j (insert i s) ∪ t, 0 ≤ p l ∧ p l ≤ 1)
    (hpi : 0 < p i) (hpj : 0 < p j) (k : ℤ)
    (hk : 0 < pbMassIntOn p s k)
    (htie : pbMassIntOn p s (k - 1) = pbMassIntOn p s k) :
    pbMassIntOn p (insert j (insert i s) ∪ t) k < pbMassIntOn p s k := by
  have hps : ∀ l ∈ s, 0 ≤ p l ∧ p l ≤ 1 :=
    fun l hl ↦ hp l (mem_union_left t (mem_insert_of_mem (mem_insert_of_mem hl)))
  have hpi' : 0 ≤ p i ∧ p i ≤ 1 := hp i (by simp)
  have hpj' : 0 ≤ p j ∧ p j ≤ 1 := hp j (by simp)
  have hj' : j ∉ insert i s := by simp [hj, Ne.symm hij]
  have hprefix := (pbMassIntOn_cross s hps).prefix_order
    (pbMassIntOn_nonneg hps) hk htie.le
  have hprefix' := pbMassIntOn_insert_prefix_order hj' hpj' k
    (pbMassIntOn_insert_prefix_order hi hpi' k hprefix)
  exact (pbMassIntOn_union_prefix_order (insert j (insert i s)) t hp k hprefix').1.trans_lt
    (pbMassIntOn_insert_insert_lt_of_tie hi hj hij hps hpi hpj k hk htie)

/-- If the target mass disappears during adjoining, every lower mass is also zero;
further additions therefore cannot recreate it. -/
theorem pbMassIntOn_zero_below_of_union_eq_zero {p : ι → ℝ} (s t : Finset ι)
    (hp : ∀ j ∈ s ∪ t, 0 ≤ p j ∧ p j ≤ 1) (k : ℤ)
    (hk : 0 < pbMassIntOn p s k)
    (hadj : pbMassIntOn p s (k - 1) ≤ pbMassIntOn p s k)
    (hzero : pbMassIntOn p (s ∪ t) k = 0) :
    ∀ j ≤ k, pbMassIntOn p (s ∪ t) j = 0 := by
  have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 := fun j hj ↦ hp j (mem_union_left t hj)
  have hprefix := (pbMassIntOn_union_prefix_order s t hp k
    ((pbMassIntOn_cross s hps).prefix_order (pbMassIntOn_nonneg hps) hk hadj)).2
  intro j hj
  apply le_antisymm
  · simpa only [hzero] using prefix_order_le hprefix hj
  · exact pbMassIntOn_nonneg hp j

/-- Once all masses through a count vanish, any further Bernoulli additions
preserve their vanishing. This algebraic implication needs no parameter bounds. -/
theorem pbMassIntOn_union_zero_of_zero_below (p : ι → ℝ) (s t : Finset ι) (k : ℤ)
    (hzero : ∀ j ≤ k, pbMassIntOn p s j = 0) :
    ∀ j ≤ k, pbMassIntOn p (s ∪ t) j = 0 := by
  induction t using Finset.induction_on with
  | empty => simpa using hzero
  | @insert i t hi ih =>
    rw [union_insert]
    by_cases him : i ∈ s ∪ t
    · simpa [insert_eq_of_mem him] using ih
    · intro j hj
      rw [pbMassIntOn_insert p him, ih j hj, ih (j - 1) (by omega)]
      ring

/-- Algebraic form of the derivative criterion: if the deleted law's adjacent
mass difference is nonpositive and the one-variable extension has positive mass,
then all further additions can only decrease that extended mass. The analytic
identification of a homogeneous derivative is a separate theorem. -/
theorem pbMassIntOn_union_le_of_deleted_adjacent {p : ι → ℝ} (s t : Finset ι)
    {i : ι} (hi : i ∉ s)
    (hp : ∀ j ∈ insert i s ∪ t, 0 ≤ p j ∧ p j ≤ 1) (k : ℤ)
    (hk : 0 < pbMassIntOn p (insert i s) k)
    (hadj : pbMassIntOn p s (k - 1) ≤ pbMassIntOn p s k) :
    pbMassIntOn p (insert i s ∪ t) k ≤ pbMassIntOn p (insert i s) k := by
  have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 :=
    fun j hj ↦ hp j (mem_union_left t (mem_insert_of_mem hj))
  have hpi : 0 ≤ p i ∧ p i ≤ 1 := hp i (by simp)
  have hbase : 0 < pbMassIntOn p s k :=
    hk.trans_le (pbMassIntOn_insert_le hi hpi.1 k hadj)
  exact pbMassIntOn_union_le_of_adjacent (insert i s) t hp k hk
    (pbMassIntOn_insert_adjacent_le hi hps hpi k hbase hadj)

end

end PoissonBinomialComparison
