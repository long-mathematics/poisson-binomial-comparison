import PoissonBinomialComparison.BenchmarkExplicit
import PoissonBinomialComparison.MinimizerReduction
import PoissonBinomialComparison.TotalVariationHomogeneous

/-!
# Benchmark attainment and the compactness reduction

The central homogeneous pair realizes the benchmark at every feasible gap,
including the endpoints. Compactness reduces the remaining comparison to
homogeneity of interior-gap global minimizers; the reduction itself makes no
assumption about stationarity or equality classification.
-/

namespace PoissonBinomialComparison

noncomputable section

/-- The benchmark agrees with the elementary two-dimensional value. -/
theorem benchmark_two {Δ : ℝ} (h0 : 0 ≤ Δ) (h2 : Δ ≤ 2) :
    benchmark 2 Δ = Δ / 2 := by
  have hh := benchmark_even_integral (m := 1) (by omega) h0 (by simpa using h2)
  norm_num at hh
  linarith

/-- Every feasible gap admits a homogeneous pair attaining the benchmark
simultaneously for the tail objective and product total variation. -/
theorem exists_homogeneous_benchmark_pair {n : ℕ} (hn : 2 ≤ n) {Δ : ℝ}
    (h0 : 0 ≤ Δ) (hnΔ : Δ ≤ n) :
    ∃ a b : ℝ, 0 ≤ b ∧ b ≤ a ∧ a ≤ 1 ∧
      meanGap (fun _ : Fin n ↦ a) (fun _ ↦ b) = Δ ∧
      tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) = benchmark n Δ ∧
      productTV (fun _ : Fin n ↦ a) (fun _ ↦ b) = benchmark n Δ := by
  have hnp : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by positivity
  rcases h0.eq_or_lt with hz | hpos
  · subst Δ
    refine ⟨0,0,le_rfl,le_rfl,by norm_num,?_,?_,?_⟩ <;>
      simp [meanGap_const]
  rcases hnΔ.eq_or_lt with heq | hlt
  · subst Δ
    refine ⟨1,0,by norm_num,by norm_num,le_rfl,?_,?_,?_⟩
    · simp [meanGap_const]
    · simp [tailObjective_const_one_zero hnp, benchmark_at_dimension hnp]
    · rw [productTV_const_eq_tailObjective n (by norm_num) (by norm_num) (by norm_num)]
      simp [tailObjective_const_one_zero hnp, benchmark_at_dimension hnp]
  · have hg0 : 0 < Δ / n := div_pos hpos hnr
    have hg1 : Δ / n < 1 := (div_lt_one hnr).mpr hlt
    have hj : 0 < n / 2 := by omega
    have hjn : n / 2 < n := by omega
    have hs := switchPair_spec hj hjn hg0 hg1
    refine ⟨switchUpper n (n/2) (Δ/n),switchLower n (n/2) (Δ/n),
      hs.1.le,hs.2.1.le,hs.2.2.1.le,?_,?_,?_⟩
    · rw [meanGap_switchPair hj hjn hg0 hg1]; field_simp
    · rw [tailObjective_switchPair hj hjn hg0 hg1,benchmark_eq_switchValue hpos hlt]
    · rw [productTV_const_eq_tailObjective n hs.1.le hs.2.1.le hs.2.2.1.le,
        tailObjective_switchPair hj hjn hg0 hg1,benchmark_eq_switchValue hpos hlt]

/-- Compactness upgrades homogeneity of all interior-gap global minimizers
in a dimension to the benchmark comparison for every pair in that dimension. -/
theorem benchmark_le_of_homogeneous_minimizers {n : ℕ} (hn : 2 ≤ n)
    (hhom : ∀ p q : Fin n → ℝ, AdmissiblePair p q → IsGapMinimizer p q →
      0 < meanGap p q → meanGap p q < n →
      ∃ a b : ℝ, p = (fun _ ↦ a) ∧ q = (fun _ ↦ b))
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) :
    benchmark n (meanGap p q) ≤ tailObjective p q := by
  have hg0 := meanGap_nonneg h
  have hgn := meanGap_le_dimension h
  rcases hg0.eq_or_lt with hz | hpos
  · rw [← hz,benchmark_zero,tailObjective_eq_zero_of_meanGap_eq_zero h hz.symm]
  rcases hgn.eq_or_lt with heq | hlt
  · rw [heq,benchmark_at_dimension (by omega),
      tailObjective_eq_one_of_meanGap_eq_dimension h (by omega) heq]
  · obtain ⟨r,s,hrs,hgap,hmin⟩ := exists_tailObjective_minimizer (meanGap p q) hg0 hgn
    have hm : IsGapMinimizer r s := by
      intro u v huv hδ
      exact hmin u v huv (hδ.trans hgap)
    obtain ⟨a,b,rfl,rfl⟩ := hhom r s hrs hm (hgap ▸ hpos) (hgap ▸ hlt)
    have hi : Fin n := ⟨0,by omega⟩
    have hh := homogeneous_minimum hn (hrs.2.1 hi).1 (hrs.2.2 hi) (hrs.1 hi).2
    rw [← meanGap_const,hgap] at hh
    exact hh.trans (hmin p q h rfl)

end

end PoissonBinomialComparison
