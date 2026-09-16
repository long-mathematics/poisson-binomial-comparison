import PoissonBinomialComparison.TailStationarity
import PoissonBinomialComparison.GapMultiplier
import PoissonBinomialComparison.GradientPositivity

/-!
# The manuscript's stationarity multipliers

Finite-maximum separation and explicit gap transfers prove the precise endpoint
signs and common-coordinate multipliers. The deletion-support argument makes
the mean-gap multiplier strictly positive. These are necessary conditions,
proved from local minimality, not assumptions about differentiability of `T`.
-/

namespace PoissonBinomialComparison

open Finset

noncomputable section

/-- The complete first-order conditions (`KKTp`, `KKTq`, `KKTC`, and `c-positive`)
for the manuscript's constrained local minimizer after boundary reduction. -/
theorem exists_tail_kkt {n : ℕ} {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    (hgap : 0 < meanGap p q) (hT : tailObjective p q < 1)
    (hmin : IsLocalMinOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2)
      (feasiblePairs n (meanGap p q)) (p,q)) :
    ∃ k : ℕ, ∃ w c : ℝ, 1 ≤ k ∧ k ≤ n ∧ 0 ≤ w ∧ w ≤ 1 ∧ 0 < c ∧
      k ∈ activeThresholds p q ∧ (w = 1 ∨ k+1 ∈ activeThresholds p q) ∧
      randomizedTail p w k-randomizedTail q w k = tailObjective p q ∧
      (∀ i, q i < p i →
        randomizedGradient p w k i ≤ c ∧ randomizedGradient q w k i ≤ c ∧
        (p i < 1 → randomizedGradient p w k i = c) ∧
        (0 < q i → randomizedGradient q w k i = c)) ∧
      (∀ i, p i = q i → ∃ ν : ℝ, 0 ≤ ν ∧
        randomizedGradient p w k i = c+ν ∧ randomizedGradient q w k i = c+ν) := by
  obtain ⟨k,w,hk0,hkn,hw0,hw1,hactive,hlast,hval,hstat⟩ :=
    exists_stationary_randomized_test h hgap hT hmin
  have hchange := exists_strict_coordinate_of_meanGap_pos h hgap
  obtain ⟨c,hc,hcommon⟩ := exists_gap_multiplier_coordinates hchange (by
    intro i hi
    exact ⟨hi ▸ hp i, hi.symm ▸ hq i⟩) hstat
  have hlast' : k < n ∨ w = 1 := by
    rcases hlast with hw | hk
    · exact Or.inr hw
    · have := ((mem_activeThresholds p q (k+1)).mp hk).2.1
      exact Or.inl (by omega)
  obtain ⟨i,hi⟩ := hchange
  have hcpos := randomizedGradient_multiplier_pos h hp hq hT hw0 hw1 hk0 hkn hlast'
    i (hc i hi).1 (hc i hi).2.1
  exact ⟨k,w,c,hk0,hkn,hw0,hw1,hcpos,hactive,hlast,hval,hc,hcommon⟩

end

end PoissonBinomialComparison
