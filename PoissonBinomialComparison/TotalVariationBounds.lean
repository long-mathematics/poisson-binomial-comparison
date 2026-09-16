import PoissonBinomialComparison.TotalVariation
import PoissonBinomialComparison.Endpoints

/-!
# Bounds and endpoint values for finite product total variation

Nonnegative normalized outcome weights give the universal upper bound one.
Together with the count-tail event bound this identifies the maximal-gap value;
the zero-gap value follows from coordinatewise equality of the parameters.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

/-- Exchanging the two product laws preserves total variation. -/
theorem productTV_symm (p q : Fin n → ℝ) : productTV p q = productTV q p := by
  simp only [productTV, abs_sub_comm]

/-- Total variation between two valid product Bernoulli laws is at most one. -/
theorem productTV_le_one (hp : ValidParameters p) (hq : ValidParameters q) :
    productTV p q ≤ 1 := by
  have hsum : (∑ A ∈ (univ : Finset (Fin n)).powerset,
      |bernoulliWeight p univ A - bernoulliWeight q univ A|) ≤
      ∑ A ∈ (univ : Finset (Fin n)).powerset,
        (bernoulliWeight p univ A + bernoulliWeight q univ A) := by
    apply sum_le_sum
    intro A hA
    have hAp : 0 ≤ bernoulliWeight p univ A :=
      bernoulliWeight_nonneg (fun i _ ↦ hp i) (mem_powerset.mp hA)
    have hAq : 0 ≤ bernoulliWeight q univ A :=
      bernoulliWeight_nonneg (fun i _ ↦ hq i) (mem_powerset.mp hA)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [sum_add_distrib, sum_bernoulliWeight, sum_bernoulliWeight] at hsum
  unfold productTV
  linarith

/-- Every admissible zero-gap pair has product total variation zero. -/
theorem productTV_eq_zero_of_meanGap_eq_zero (h : AdmissiblePair p q)
    (hgap : meanGap p q = 0) : productTV p q = 0 := by
  rw [(meanGap_eq_zero_iff h).mp hgap]
  exact productTV_self q

/-- Every admissible maximal-gap pair has product total variation one
in positive dimension. -/
theorem productTV_eq_one_of_meanGap_eq_dimension (h : AdmissiblePair p q)
    (hn : 0 < n) (hgap : meanGap p q = n) : productTV p q = 1 := by
  apply le_antisymm (productTV_le_one h.1 h.2.1)
  rw [← tailObjective_eq_one_of_meanGap_eq_dimension h hn hgap]
  exact tailObjective_le_productTV p q

/-- The opposite deterministic vectors have total variation one. -/
theorem productTV_const_one_zero (hn : 0 < n) :
    productTV (fun _ : Fin n ↦ (1 : ℝ)) (fun _ ↦ 0) = 1 := by
  apply productTV_eq_one_of_meanGap_eq_dimension
  · rw [admissiblePair_iff]
    intro i
    norm_num
  · exact hn
  · simp [meanGap]

end

end PoissonBinomialComparison
