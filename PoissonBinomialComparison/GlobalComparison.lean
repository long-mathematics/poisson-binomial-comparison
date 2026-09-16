import PoissonBinomialComparison.GlobalHomogeneity
import PoissonBinomialComparison.BenchmarkAttainment
import PoissonBinomialComparison.HomogeneousEquality

/-!
# The global comparison and equality classification

Induction begins with the exact two-dimensional value. Compactness and the
proved minimizer homogeneity close each higher-dimensional step. The equality
statements use canonical switches, with explicit even and odd formulations.
-/

namespace PoissonBinomialComparison

noncomputable section

/-- The manuscript's sharp tail comparison, including both gap endpoints. -/
theorem benchmark_le_tailObjective {n : ℕ} (hn : 2 ≤ n)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) :
    benchmark n (meanGap p q) ≤ tailObjective p q := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [benchmark_two (meanGap_nonneg h) (by simpa using meanGap_le_dimension h)]
    exact twoDimensional_lower_bound p q
  | succ n hn ih =>
    apply benchmark_le_of_homogeneous_minimizers (by omega) ?_ h
    intro r s hrs hm hg0 hgn
    have hind : ∀ u v : Fin (n+1-1) → ℝ, AdmissiblePair u v →
        benchmark (n+1-1) (meanGap u v) ≤ tailObjective u v := by
      rw [show n+1-1=n by omega]
      exact fun _ _ huv ↦ ih huv
    obtain ⟨a,b,_,_,_,hp,hq⟩ := hm.homogeneous (by omega) hind hrs hg0 hgn
    exact ⟨a,b,hp,hq⟩

/-- A global minimizer at an interior gap in dimension at least three is
fully homogeneous with strictly interior, strictly ordered parameters. -/
theorem IsGapMinimizer.homogeneous_of_interior_gap {n : ℕ} (hn : 3 ≤ n)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n) :
    ∃ a b : ℝ, 0 < b ∧ b < a ∧ a < 1 ∧ p = (fun _ ↦ a) ∧ q = (fun _ ↦ b) :=
  hm.homogeneous hn (fun _ _ hh ↦ benchmark_le_tailObjective (by omega) hh) h hg0 hgn

/-- Equality in the sharp comparison is exactly the central homogeneous pair
or its reflection. The formulation applies uniformly to odd and even dimensions. -/
theorem tailObjective_eq_benchmark_iff {n : ℕ} (hn : 3 ≤ n)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) {Δ : ℝ} (hgap : meanGap p q = Δ)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    tailObjective p q = benchmark n Δ ↔
      (p = (fun _ ↦ switchUpper n (n/2) (Δ/n)) ∧
        q = (fun _ ↦ switchLower n (n/2) (Δ/n))) ∨
      (p = (fun _ ↦ 1-switchLower n (n/2) (Δ/n)) ∧
        q = (fun _ ↦ 1-switchUpper n (n/2) (Δ/n))) := by
  have hnr : (0 : ℝ) < n := by positivity
  have hg0 : 0 < Δ/n := div_pos hΔ0 hnr
  have hg1 : Δ/n < 1 := (div_lt_one hnr).mpr hΔn
  have hj : 0 < n/2 := by omega
  have hjn : n/2 < n := by omega
  constructor
  · intro heq
    have hm : IsGapMinimizer p q := by
      intro r s hrs hδ
      rw [heq,← hδ.trans hgap]
      exact benchmark_le_tailObjective (by omega) hrs
    obtain ⟨a,b,hb,hba,ha,rfl,rfl⟩ := hm.homogeneous_of_interior_gap hn h
      (hgap ▸ hΔ0) (hgap ▸ hΔn)
    have hγ : Δ/n = a-b := by rw [← hgap,meanGap_const]; field_simp
    have he := (homogeneous_minimum_eq_canonical_iff (by omega : 2 ≤ n) hb.le ha.le
      (sub_pos.mpr hba) (by linarith)).mp (by rwa [← meanGap_const,hgap])
    rw [hγ]
    rcases he with ⟨ha',hb'⟩ | ⟨ha',hb'⟩
    · exact Or.inl ⟨funext (fun _ ↦ ha'),funext (fun _ ↦ hb')⟩
    · exact Or.inr ⟨funext (fun _ ↦ ha'),funext (fun _ ↦ hb')⟩
  · have hc : tailObjective (fun _ : Fin n ↦ switchUpper n (n/2) (Δ/n))
        (fun _ ↦ switchLower n (n/2) (Δ/n)) = benchmark n Δ := by
      rw [tailObjective_switchPair hj hjn hg0 hg1,benchmark_eq_switchValue hΔ0 hΔn]
    rintro (⟨hp,hq⟩ | ⟨hp,hq⟩)
    · rw [hp,hq]; exact hc
    · rw [hp,hq,tailObjective_reflection]; exact hc

/-- The even-dimensional equality formula exactly as stated in the paper. -/
theorem tailObjective_even_eq_benchmark_iff {m : ℕ} (hm : 2 ≤ m)
    {p q : Fin (2*m) → ℝ} (h : AdmissiblePair p q) {Δ : ℝ}
    (hgap : meanGap p q = Δ) (hΔ0 : 0 < Δ) (hΔn : Δ < 2*m) :
    tailObjective p q = benchmark (2*m) Δ ↔
      p = (fun _ ↦ (1+Δ/(2*m))/2) ∧ q = (fun _ ↦ (1-Δ/(2*m))/2) := by
  have hnr : (0 : ℝ) < 2*m := by positivity
  have he := switchPair_even (by omega : 0 < m) (div_pos hΔ0 hnr)
    ((div_lt_one hnr).mpr hΔn)
  have hh := tailObjective_eq_benchmark_iff (by omega : 3 ≤ 2*m) h hgap hΔ0
    (by exact_mod_cast hΔn)
  simp only [show 2*m/2=m by omega,Nat.cast_mul,Nat.cast_ofNat,he.1,he.2] at hh
  have h1 : 1-(1-Δ/(2*m))/2 = (1+Δ/(2*m))/2 := by ring
  have h2 : 1-(1+Δ/(2*m))/2 = (1-Δ/(2*m))/2 := by ring
  simpa only [h1,h2,or_self] using hh

/-- The odd-dimensional equality formula for any pair solving the central
switch equations, rather than only the chosen canonical representatives. -/
theorem tailObjective_odd_eq_benchmark_iff {m : ℕ} (hm : 0 < m)
    {p q : Fin (2*m+1) → ℝ} (h : AdmissiblePair p q) {Δ a b : ℝ}
    (hgap : meanGap p q = Δ) (hΔ0 : 0 < Δ) (hΔn : Δ < 2*m+1)
    (hs : IsSwitch (2*m+1) m (Δ/(2*m+1)) a b) :
    tailObjective p q = benchmark (2*m+1) Δ ↔
      (p = (fun _ ↦ a) ∧ q = (fun _ ↦ b)) ∨
      (p = (fun _ ↦ 1-b) ∧ q = (fun _ ↦ 1-a)) := by
  obtain ⟨ha,hb⟩ := hs.eq_switchPair hm (by omega)
  have hh := tailObjective_eq_benchmark_iff (by omega : 3 ≤ 2*m+1) h hgap hΔ0
    (by exact_mod_cast hΔn)
  simpa only [show (2*m+1)/2=m by omega,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    Nat.cast_one,← ha,← hb] using hh

end

end PoissonBinomialComparison
