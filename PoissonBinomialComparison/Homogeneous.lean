import PoissonBinomialComparison.Switch

/-!
# Homogeneous parameters and binomial masses

Specializing the subset-sum law to a constant parameter gives the familiar
binomial formula, including counts above the support. These identities are
algebraic and do not require the parameter to lie in `[0, 1]`.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

variable {ι : Type*} [DecidableEq ι]

/-- A homogeneous outcome has weight determined by its cardinality. -/
theorem bernoulliWeight_const (t : ℝ) {s A : Finset ι} (hA : A ⊆ s) :
    bernoulliWeight (fun _ ↦ t) s A = t ^ A.card * (1 - t) ^ (s.card - A.card) := by
  simp [bernoulliWeight, card_sdiff_of_subset hA]

/-- The homogeneous subset sum equals a binomial mass on any finite coordinate set. -/
theorem pbMassOn_const (t : ℝ) (s : Finset ι) (k : ℕ) :
    pbMassOn (fun _ ↦ t) s k =
      (s.card.choose k : ℝ) * t ^ k * (1 - t) ^ (s.card - k) := by
  unfold pbMassOn
  calc
    _ = ∑ _A ∈ s.powersetCard k, t ^ k * (1 - t) ^ (s.card - k) := by
      apply sum_congr rfl
      intro A hA
      rw [bernoulliWeight_const t (mem_powersetCard.mp hA).1,
        (mem_powersetCard.mp hA).2]
    _ = _ := by simp [card_powersetCard, mul_assoc]

/-- Homogeneous count masses are the binomial masses, for every natural count. -/
theorem pbMass_const (n k : ℕ) (t : ℝ) :
    pbMass (fun _ : Fin n ↦ t) k =
      (n.choose k : ℝ) * t ^ k * (1 - t) ^ (n - k) := by
  simpa [pbMass] using pbMassOn_const t (univ : Finset (Fin n)) k

/-- The homogeneous tail on a finite coordinate set is a finite binomial sum. -/
theorem pbTailOn_const (t : ℝ) (s : Finset ι) (k : ℕ) :
    pbTailOn (fun _ ↦ t) s k =
      ∑ j ∈ Icc k s.card, (s.card.choose j : ℝ) * t ^ j * (1 - t) ^ (s.card - j) := by
  simp only [pbTailOn_eq_sum_mass, pbMassOn_const]

/-- Homogeneous tails are the usual binomial upper tails. -/
theorem pbTail_const (n k : ℕ) (t : ℝ) :
    pbTail (fun _ : Fin n ↦ t) k =
      ∑ j ∈ Icc k n, (n.choose j : ℝ) * t ^ j * (1 - t) ^ (n - j) := by
  simp only [pbTail_eq_sum_mass, pbMass_const]

/-- The homogeneous mean gap is dimension times the coordinate gap. -/
theorem meanGap_const (n : ℕ) (a b : ℝ) :
    meanGap (fun _ : Fin n ↦ a) (fun _ : Fin n ↦ b) = n * (a - b) := by
  simp [meanGap, mul_sub]

/-- The switch equation is equivalent to equality of the two binomial count masses. -/
theorem pbMass_const_eq_iff {n j : ℕ} (hj : j ≤ n) (a b : ℝ) :
    pbMass (fun _ : Fin n ↦ a) j = pbMass (fun _ : Fin n ↦ b) j ↔
      a ^ j * (1 - a) ^ (n - j) = b ^ j * (1 - b) ^ (n - j) := by
  have hchoose : (n.choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj).ne'
  simp only [pbMass_const, mul_assoc]
  exact ⟨mul_left_cancel₀ hchoose, congrArg ((n.choose j : ℝ) * ·)⟩

/-- A switch has equal count masses at its switching count. -/
theorem IsSwitch.pbMass_eq {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b) :
    pbMass (fun _ : Fin n ↦ a) j = pbMass (fun _ : Fin n ↦ b) j := by
  simp only [pbMass_const, mul_assoc, h.2.2.2.2]

end PoissonBinomialComparison
