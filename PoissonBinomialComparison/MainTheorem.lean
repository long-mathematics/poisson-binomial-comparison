import PoissonBinomialComparison.GlobalComparison
import PoissonBinomialComparison.TotalVariationBounds
import PoissonBinomialComparison.TwoDimensionalEquality

/-!
# The manuscript's main theorem

The tail and product total-variation comparisons have the same sharp benchmark.
Every feasible gap attains both minima. In dimension at least three, the two
objectives have exactly the same equality cases, given explicitly in even and
odd dimensions below. The endpoint and exceptional two-dimensional statements
are included through their already proved modules.
-/

namespace PoissonBinomialComparison

noncomputable section

/-- Sharp product total-variation comparison for every admissible pair. -/
theorem benchmark_le_productTV {n : ℕ} (hn : 2 ≤ n)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) :
    benchmark n (meanGap p q) ≤ productTV p q :=
  (benchmark_le_tailObjective hn h).trans (tailObjective_le_productTV p q)

/-- The two comparisons in the main theorem, including both gap endpoints. -/
theorem main_comparison {n : ℕ} (hn : 2 ≤ n)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) :
    benchmark n (meanGap p q) ≤ tailObjective p q ∧
      benchmark n (meanGap p q) ≤ productTV p q :=
  ⟨benchmark_le_tailObjective hn h, benchmark_le_productTV hn h⟩

/-- Both exact minima are attained at every feasible prescribed gap. -/
theorem benchmark_exact_minima {n : ℕ} (hn : 2 ≤ n) {Δ : ℝ}
    (h0 : 0 ≤ Δ) (hnΔ : Δ ≤ n) :
    ∃ p q : Fin n → ℝ, AdmissiblePair p q ∧ meanGap p q = Δ ∧
      tailObjective p q = benchmark n Δ ∧ productTV p q = benchmark n Δ ∧
      ∀ r s : Fin n → ℝ, AdmissiblePair r s → meanGap r s = Δ →
        benchmark n Δ ≤ tailObjective r s ∧ benchmark n Δ ≤ productTV r s := by
  obtain ⟨a,b,hb,hba,ha,hgap,ht,hv⟩ := exists_homogeneous_benchmark_pair hn h0 hnΔ
  refine ⟨(fun _ ↦ a),(fun _ ↦ b),?_,hgap,ht,hv,?_⟩
  · rw [admissiblePair_iff]
    exact fun _ ↦ ⟨hb,hba,ha⟩
  · intro r s hrs hδ
    simpa only [hδ] using main_comparison hn hrs

/-- For an interior gap in dimension at least three, product equality is
exactly tail equality; both directions include all admissible parameter pairs. -/
theorem productTV_eq_benchmark_iff_tail {n : ℕ} (hn : 3 ≤ n)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) {Δ : ℝ} (hgap : meanGap p q = Δ)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    productTV p q = benchmark n Δ ↔ tailObjective p q = benchmark n Δ := by
  constructor
  · intro heq
    have hlo := benchmark_le_tailObjective (by omega : 2 ≤ n) h
    rw [hgap] at hlo
    exact le_antisymm ((tailObjective_le_productTV p q).trans_eq heq) hlo
  · intro heq
    have hm : IsGapMinimizer p q := by
      intro r s hrs hδ
      rw [heq,← hδ.trans hgap]
      exact benchmark_le_tailObjective (by omega) hrs
    obtain ⟨a,b,hb,hba,ha,rfl,rfl⟩ := hm.homogeneous_of_interior_gap hn h
      (hgap ▸ hΔ0) (hgap ▸ hΔn)
    rw [productTV_const_eq_tailObjective n hb.le hba.le ha.le]
    exact heq

/-- All product equality cases: the central homogeneous pair and its reflection. -/
theorem productTV_eq_benchmark_iff {n : ℕ} (hn : 3 ≤ n)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) {Δ : ℝ} (hgap : meanGap p q = Δ)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    productTV p q = benchmark n Δ ↔
      (p = (fun _ ↦ switchUpper n (n/2) (Δ/n)) ∧
        q = (fun _ ↦ switchLower n (n/2) (Δ/n))) ∨
      (p = (fun _ ↦ 1-switchLower n (n/2) (Δ/n)) ∧
        q = (fun _ ↦ 1-switchUpper n (n/2) (Δ/n))) :=
  (productTV_eq_benchmark_iff_tail hn h hgap hΔ0 hΔn).trans
    (tailObjective_eq_benchmark_iff hn h hgap hΔ0 hΔn)

/-- The unique even-dimensional product equality pair in the manuscript. -/
theorem productTV_even_eq_benchmark_iff {m : ℕ} (hm : 2 ≤ m)
    {p q : Fin (2*m) → ℝ} (h : AdmissiblePair p q) {Δ : ℝ}
    (hgap : meanGap p q = Δ) (hΔ0 : 0 < Δ) (hΔn : Δ < 2*m) :
    productTV p q = benchmark (2*m) Δ ↔
      p = (fun _ ↦ (1+Δ/(2*m))/2) ∧ q = (fun _ ↦ (1-Δ/(2*m))/2) :=
  (productTV_eq_benchmark_iff_tail (by omega : 3 ≤ 2*m) h hgap hΔ0
    (by exact_mod_cast hΔn)).trans (tailObjective_even_eq_benchmark_iff hm h hgap hΔ0 hΔn)

/-- The two reflected odd-dimensional product equality pairs in the manuscript. -/
theorem productTV_odd_eq_benchmark_iff {m : ℕ} (hm : 0 < m)
    {p q : Fin (2*m+1) → ℝ} (h : AdmissiblePair p q) {Δ a b : ℝ}
    (hgap : meanGap p q = Δ) (hΔ0 : 0 < Δ) (hΔn : Δ < 2*m+1)
    (hs : IsSwitch (2*m+1) m (Δ/(2*m+1)) a b) :
    productTV p q = benchmark (2*m+1) Δ ↔
      (p = (fun _ ↦ a) ∧ q = (fun _ ↦ b)) ∨
      (p = (fun _ ↦ 1-b) ∧ q = (fun _ ↦ 1-a)) :=
  (productTV_eq_benchmark_iff_tail (by omega : 3 ≤ 2*m+1) h hgap hΔ0
    (by exact_mod_cast hΔn)).trans (tailObjective_odd_eq_benchmark_iff hm h hgap hΔ0 hΔn hs)

/-- At zero gap all admissible pairs coincide and both objectives equal zero. -/
theorem main_zero_gap {n : ℕ} {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (hgap : meanGap p q = 0) :
    p = q ∧ tailObjective p q = 0 ∧ productTV p q = 0 :=
  ⟨(meanGap_eq_zero_iff h).mp hgap,tailObjective_eq_zero_of_meanGap_eq_zero h hgap,
    productTV_eq_zero_of_meanGap_eq_zero h hgap⟩

/-- At maximal gap feasibility forces the opposite deterministic vectors. -/
theorem main_maximal_gap {n : ℕ} (hn : 0 < n) {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hgap : meanGap p q = n) :
    p = (fun _ ↦ 1) ∧ q = (fun _ ↦ 0) ∧ tailObjective p q = 1 ∧ productTV p q = 1 :=
  ⟨((meanGap_eq_dimension_iff h).mp hgap).1,((meanGap_eq_dimension_iff h).mp hgap).2,
    tailObjective_eq_one_of_meanGap_eq_dimension h hn hgap,
    productTV_eq_one_of_meanGap_eq_dimension h hn hgap⟩

end

end PoissonBinomialComparison
