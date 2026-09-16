import PoissonBinomialComparison.TotalVariationHomogeneous
import PoissonBinomialComparison.SwitchFunctions

/-! # Switching counts attain the tail objective -/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

/-- A common positive atom makes the finite product laws' total variation
strictly less than one. -/
theorem productTV_lt_one_of_common_atom (hp : ValidParameters p) (hq : ValidParameters q)
    (A : Finset (Fin n)) (hAp : 0 < bernoulliWeight p univ A)
    (hAq : 0 < bernoulliWeight q univ A) : productTV p q < 1 := by
  have hs : (∑ B ∈ (univ : Finset (Fin n)).powerset,
      |bernoulliWeight p univ B - bernoulliWeight q univ B|) <
      ∑ B ∈ (univ : Finset (Fin n)).powerset,
        (bernoulliWeight p univ B + bernoulliWeight q univ B) := by
    apply sum_lt_sum
    · intro B hB
      have hBp := bernoulliWeight_nonneg (fun i _ ↦ hp i) (mem_powerset.mp hB)
      have hBq := bernoulliWeight_nonneg (fun i _ ↦ hq i) (mem_powerset.mp hB)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact ⟨A, by simp, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  rw [sum_add_distrib, sum_bernoulliWeight, sum_bernoulliWeight] at hs
  unfold productTV
  linarith

/-- Equal positive masses in an ordered pair identify a maximizing threshold. -/
theorem tailObjective_eq_tailDiff_of_equal_mass (h : AdmissiblePair p q) (k : ℕ)
    (heq : pbMass p k = pbMass q k) (hpos : 0 < pbMass q k) :
    tailObjective p q = tailDiff p q k := by
  rw [← countTV_eq_tailObjective h]
  apply countTV_eq_tailDiff_of_signs
  · intro l hl
    apply (mul_le_mul_iff_left₀ hpos).mp
    simpa [heq, mul_comm] using pbMass_likelihoodRatio h l k hl.le
  · intro l hl
    apply (mul_le_mul_iff_left₀ hpos).mp
    simpa [heq, mul_comm] using pbMass_likelihoodRatio h k l hl

/-- Every interior switch attains its exact tail objective at its switching count. -/
theorem IsSwitch.tailObjective_eq {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (_hj : 0 < j) (hjn : j < n) :
    tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) =
      tailDiff (fun _ : Fin n ↦ a) (fun _ ↦ b) j := by
  apply tailObjective_eq_tailDiff_of_equal_mass
    ((admissiblePair_iff _ _).mpr (fun _ ↦ ⟨h.1.le, h.2.1.le, h.2.2.1.le⟩)) j h.pbMass_eq
  rw [pbMass_const]
  have hc : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos hjn.le
  exact mul_pos (mul_pos hc (pow_pos h.1 _)) (pow_pos (by linarith [h.2.1, h.2.2.1]) _)

/-- The canonical switch value is the exact maximum of all count-tail differences. -/
theorem tailObjective_switchPair {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    tailObjective (fun _ : Fin n ↦ switchUpper n j γ)
      (fun _ ↦ switchLower n j γ) = switchValue n j γ :=
  (switchPair_spec hj hjn hγ0 hγ1).tailObjective_eq hj hjn

/-- Interior homogeneous switches have overlapping product laws and objective below one. -/
theorem IsSwitch.tailObjective_lt_one {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) :
    tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) < 1 := by
  have hp : ValidParameters (fun _ : Fin n ↦ a) :=
    fun _ ↦ ⟨(h.1.trans h.2.1).le, h.2.2.1.le⟩
  have hq : ValidParameters (fun _ : Fin n ↦ b) :=
    fun _ ↦ ⟨h.1.le, (h.2.1.trans h.2.2.1).le⟩
  apply (tailObjective_le_productTV _ _).trans_lt
    (productTV_lt_one_of_common_atom hp hq ∅ ?_ ?_)
  · simp [bernoulliWeight]
    exact pow_pos (sub_pos.mpr h.2.2.1) n
  · simp [bernoulliWeight]
    exact pow_pos (sub_pos.mpr (h.2.1.trans h.2.2.1)) n

/-- Exactly the two adjacent thresholds maximize at an interior switch. -/
theorem IsSwitch.activeThresholds_eq {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (hj : 0 < j) (hjn : j < n) :
    activeThresholds (fun _ : Fin n ↦ a) (fun _ ↦ b) = {j, j + 1} := by
  let p : Fin n → ℝ := fun _ ↦ a
  let q : Fin n → ℝ := fun _ ↦ b
  have hpq : AdmissiblePair p q :=
    (admissiblePair_iff _ _).mpr (fun _ ↦ ⟨h.1.le, h.2.1.le, h.2.2.1.le⟩)
  have hgap : 0 < meanGap p q := by
    rw [meanGap_const]
    exact mul_pos (by exact_mod_cast (show 0 < n by omega)) (sub_pos.mpr h.2.1)
  have hmax : tailObjective p q = tailDiff p q j := h.tailObjective_eq hj hjn
  have hjmem : j ∈ activeThresholds p q :=
    (mem_activeThresholds p q j).mpr ⟨hj, hjn.le, hmax.symm⟩
  have hjmem' : j + 1 ∈ activeThresholds p q :=
    (mem_activeThresholds p q (j + 1)).mpr ⟨by omega, by omega,
      h.tailDiff_eq.symm.trans hmax.symm⟩
  ext k
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hk
    have hleft := activeThresholds_distance_le_one hpq hgap h.tailObjective_lt_one hk hjmem'
    have hright := activeThresholds_distance_le_one hpq hgap h.tailObjective_lt_one hjmem hk
    omega
  · rintro (rfl | rfl)
    · exact hjmem
    · exact hjmem'

end

end PoissonBinomialComparison
