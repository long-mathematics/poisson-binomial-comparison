import PoissonBinomialComparison.ActiveThresholds
import PoissonBinomialComparison.ParameterDerivative
import PoissonBinomialComparison.FeasibleDirections
import PoissonBinomialComparison.ConvexStationarity

/-!
# First-order stationarity of the exact tail maximum

Inactive thresholds stay strictly separated on a neighborhood. Separating the
active directional gradients on the actual feasible cone gives the manuscript's
randomized test, without assuming differentiability of the maximum itself.
-/

namespace PoissonBinomialComparison

open scoped BigOperators Topology
open Finset Filter

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

/-- A maximum with at most two active thresholds equals their maximum locally. -/
theorem tailObjective_eventually_eq_max {k l : ℕ} (hk : k ∈ activeThresholds p q)
    (hl : l ∈ Icc 1 n) (hactive : activeThresholds p q ⊆ {k,l}) :
    (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2) =ᶠ[𝓝 (p,q)]
      (fun x ↦ max (tailDiff x.1 x.2 k) (tailDiff x.1 x.2 l)) := by
  have hk' := (mem_activeThresholds p q k).mp hk
  have hn : 0 < n := by omega
  have he : ∀ h ∈ Icc 1 n, ∀ᶠ x : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (p,q),
      tailDiff x.1 x.2 h ≤ max (tailDiff x.1 x.2 k) (tailDiff x.1 x.2 l) := by
    intro h hh
    by_cases hhk : h = k
    · subst h
      exact Eventually.of_forall (fun _ ↦ le_max_left _ _)
    by_cases hhl : h = l
    · subst h
      exact Eventually.of_forall (fun _ ↦ le_max_right _ _)
    have hlt : tailDiff p q h < tailDiff p q k := by
      have hle := tailDiff_le_tailObjective p q hh
      rw [← hk'.2.2] at hle
      apply lt_of_le_of_ne hle
      intro heq
      have hm : h ∈ activeThresholds p q := mem_filter.mpr ⟨hh, heq.trans hk'.2.2⟩
      have := hactive hm
      simp only [mem_insert, mem_singleton] at this
      exact this.elim hhk hhl
    exact ((continuous_tailDiff h).continuousAt.eventually_lt
      (continuous_tailDiff k).continuousAt hlt).mono
      (fun _ ht ↦ ht.le.trans (le_max_left _ _))
  have hall : ∀ᶠ x : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (p,q),
      ∀ h ∈ Icc 1 n, tailDiff x.1 x.2 h ≤ max (tailDiff x.1 x.2 k) (tailDiff x.1 x.2 l) := by
    rw [eventually_all_finset]
    exact he
  filter_upwards [hall] with x hx
  apply le_antisymm
  · exact (tailObjective_le_iff x.1 x.2 hn _).mpr hx
  · exact max_le (tailDiff_le_tailObjective x.1 x.2 (mem_Icc.mpr ⟨hk'.1,hk'.2.1⟩))
      (tailDiff_le_tailObjective x.1 x.2 hl)

/-- Separation of the two active gradients on the true fixed-gap direction set. -/
theorem exists_supporting_tail_gradients (h : AdmissiblePair p q)
    (hmin : IsLocalMinOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2)
      (feasiblePairs n (meanGap p q)) (p,q))
    {k l : ℕ} (hk : k ∈ activeThresholds p q) (hl : l ∈ Icc 1 n)
    (hactive : activeThresholds p q ⊆ {k,l}) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ ∀ d ∈ feasibleDirections p q,
      0 ≤ w * fderiv ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailDiff x.1 x.2 k) (p,q) d +
        (1-w) * fderiv ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailDiff x.1 x.2 l) (p,q) d := by
  have heq := tailObjective_eventually_eq_max hk hl hactive
  have hm := hmin.congr (heq.filter_mono nhdsWithin_le_nhds) (show (p,q) ∈
    feasiblePairs n (meanGap p q) from ⟨h,rfl⟩)
  exact exists_supporting_gradient_of_localMinOn
    ((differentiable_tailDiff k) (p,q)).hasFDerivAt
    ((differentiable_tailDiff l) (p,q)).hasFDerivAt hm
    (convex_feasibleDirections p q) (zero_mem_feasibleDirections p q)
    (fun _ hd ↦ eventually_mem_feasiblePairs_of_direction h hd)

/-- The manuscript's active randomized test exists at every constrained local
minimum with positive gap and objective below one. Its gradient is nonnegative
on every feasible direction; multiplier coordinates are derived separately. -/
theorem exists_stationary_randomized_test (h : AdmissiblePair p q)
    (hgap : 0 < meanGap p q) (hT : tailObjective p q < 1)
    (hmin : IsLocalMinOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2)
      (feasiblePairs n (meanGap p q)) (p,q)) :
    ∃ k : ℕ, ∃ w : ℝ, 1 ≤ k ∧ k ≤ n ∧ 0 ≤ w ∧ w ≤ 1 ∧
      k ∈ activeThresholds p q ∧ (w = 1 ∨ k+1 ∈ activeThresholds p q) ∧
      randomizedTail p w k-randomizedTail q w k = tailObjective p q ∧
      ∀ d ∈ feasibleDirections p q,
        0 ≤ ∑ i, (d.1 i*randomizedGradient p w k i-d.2 i*randomizedGradient q w k i) := by
  obtain ⟨k,hk0,hkn,hactive⟩ := activeThresholds_singleton_or_adjacent h hgap hT
  have hkr : k ∈ Icc 1 n := mem_Icc.mpr ⟨hk0,hkn⟩
  rcases hactive with hone | ⟨hk1,htwo⟩
  · have hk : k ∈ activeThresholds p q := by rw [hone]; simp
    have hsub : activeThresholds p q ⊆ {k,k} := by simp [hone]
    obtain ⟨w,_,_,hw⟩ := exists_supporting_tail_gradients h hmin hk hkr hsub
    refine ⟨k,1,hk0,hkn,by norm_num,le_rfl,hk,Or.inl rfl,?_,?_⟩
    · simpa [randomizedDiff_eq] using (mem_activeThresholds p q k).mp hk |>.2.2
    · intro d hd
      have hv := hw d hd
      rw [← weighted_fderiv_tailDiff_apply p q d.1 d.2 1 k]
      simp only [one_mul, sub_self, zero_mul, add_zero]
      nlinarith
  · have hk : k ∈ activeThresholds p q := by rw [htwo]; simp
    have hl : k+1 ∈ activeThresholds p q := by rw [htwo]; simp
    obtain ⟨w,hw0,hw1,hw⟩ := exists_supporting_tail_gradients h hmin hk
      (mem_Icc.mpr ⟨by omega,hk1⟩) (by rw [htwo])
    refine ⟨k,w,hk0,hkn,hw0,hw1,hk,Or.inr hl,?_,?_⟩
    · rw [randomizedDiff_eq, ((mem_activeThresholds p q k).mp hk).2.2,
        ((mem_activeThresholds p q (k+1)).mp hl).2.2]
      ring
    · intro d hd
      rw [← weighted_fderiv_tailDiff_apply p q d.1 d.2 w k]
      exact hw d hd

end

end PoissonBinomialComparison
