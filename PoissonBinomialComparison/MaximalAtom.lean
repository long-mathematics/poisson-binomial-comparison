import PoissonBinomialComparison.BinomialAtom
import PoissonBinomialComparison.Deterministic
import PoissonBinomialComparison.Reindex
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The maximal-atom bound

At integer mean, the fixed-mean extremizer reduction and the numerical binomial
bound give the manuscript's lower bound `κ_n`. For an arbitrary `m`-trial law,
one extra Bernoulli parameter completes its mean to an integer. The new mass is
a convex combination of two old masses, so one old mass is at least `κ_(m+1)`.
All deterministic and empty-dimensional cases are included.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ}

/-- An integer-mean `n`-trial Bernoulli law has mass at least `κ_n` at its mean. -/
theorem kappa_le_pbMass_at_integer_mean {p : Fin n → ℝ} (hp : ValidParameters p)
    (k : ℕ) (hmean : (∑ i, p i) = k) : kappa n ≤ pbMass p k := by
  obtain ⟨M, ℓ, hM, hℓ, hmass⟩ := exists_binomial_mass_le_integer_mean_mass hp k hmean
  exact (kappa_le_pbMass_integerMean hℓ hM).trans hmass

/-- Every `n`-trial law has a mass at least `κ_(n+1)`, at a count in its support range. -/
theorem exists_pbMass_ge_kappa_succ {p : Fin n → ℝ} (hp : ValidParameters p) :
    ∃ k : ℕ, k ≤ n ∧ kappa (n + 1) ≤ pbMass p k := by
  let μ : ℝ := ∑ i, p i
  have hμ : 0 ≤ μ := sum_nonneg (fun i _ ↦ (hp i).1)
  let k : ℕ := ⌊μ⌋₊
  let t : ℝ := (k : ℝ) + 1 - μ
  have hfloor : (k : ℝ) ≤ μ := Nat.floor_le hμ
  have hceil : μ < (k : ℝ) + 1 := Nat.lt_floor_add_one μ
  have ht : 0 ≤ t ∧ t ≤ 1 := by dsimp [t]; constructor <;> linarith
  have hvalid : ValidParameters (Fin.cons t p) := by
    intro i
    exact Fin.cases ht hp i
  have hmean : (∑ i, Fin.cons t p i) = ((k + 1 : ℕ) : ℝ) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Nat.cast_add, Nat.cast_one]
    change t + μ = (k : ℝ) + 1
    dsimp [t]
    ring
  have hnew := kappa_le_pbMass_at_integer_mean hvalid (k + 1) hmean
  have hrec : pbMass (Fin.cons t p) (k + 1) =
      (1 - t) * pbMass p (k + 1) + t * pbMass p k := by
    have h := pbMassInt_cons p t ((k + 1 : ℕ) : ℤ)
    have hc : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
    simpa only [hc, pbMassIntOn_natCast, pbMass] using h
  rw [hrec] at hnew
  have hmax : kappa (n + 1) ≤ max (pbMass p (k + 1)) (pbMass p k) := by
    have h1 := mul_le_mul_of_nonneg_left (le_max_left (pbMass p (k + 1)) (pbMass p k))
      (sub_nonneg.mpr ht.2)
    have h2 := mul_le_mul_of_nonneg_left (le_max_right (pbMass p (k + 1)) (pbMass p k)) ht.1
    nlinarith
  have hsupport : ∀ j : ℕ, kappa (n + 1) ≤ pbMass p j → j ≤ n := by
    intro j hj
    by_contra hnj
    have hz := pbMass_eq_zero_of_lt p (show n < j by omega)
    rw [hz] at hj
    exact (not_le_of_gt (kappa_pos (n + 1))) hj
  rcases le_max_iff.mp hmax with hnext | hprev
  · exact ⟨k + 1, hsupport (k + 1) hnext, hnext⟩
  · exact ⟨k, hsupport k hprev, hprev⟩

/-- The manuscript's maximal-atom assertion in its original dimension notation. -/
theorem exists_pbMass_ge_kappa (n : ℕ) (hn : 1 ≤ n)
    {p : Fin (n - 1) → ℝ} (hp : ValidParameters p) :
    ∃ k : ℕ, k ≤ n - 1 ∧ kappa n ≤ pbMass p k := by
  simpa only [Nat.sub_add_cancel hn] using exists_pbMass_ge_kappa_succ hp

variable {ι : Type*} [DecidableEq ι]

/-- Integer-mean atom bound for a finite coordinate set, without relabelling in the statement. -/
theorem kappa_le_pbMassOn_at_integer_mean {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (k : ℕ)
    (hmean : (∑ i ∈ s, p i) = k) : kappa s.card ≤ pbMassOn p s k := by
  have h := kappa_le_pbMass_at_integer_mean (valid_finsetParameters s hp) k
    (by rw [sum_finsetParameters]; exact hmean)
  simpa only [pbMass_finsetParameters] using h

/-- Maximal-atom bound on an arbitrary finite coordinate set. -/
theorem exists_pbMassOn_ge_kappa_succ {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) :
    ∃ k : ℕ, k ≤ s.card ∧ kappa (s.card + 1) ≤ pbMassOn p s k := by
  simpa only [pbMass_finsetParameters] using
    exists_pbMass_ge_kappa_succ (valid_finsetParameters s hp)

end

end PoissonBinomialComparison
