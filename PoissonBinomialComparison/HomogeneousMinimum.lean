import PoissonBinomialComparison.HomogeneousMinimizer
import PoissonBinomialComparison.SwitchOrdering

/-!
# The exact homogeneous minimum

Compactness and the exclusion of nonswitch local minima reduce the problem to
switches. Strict ordering of switch values then identifies exactly the central
switch and its reflection. No global inhomogeneous comparison is used here.
-/

namespace PoissonBinomialComparison

noncomputable section

/-- Any interior switch attains its canonical switching value. -/
theorem IsSwitch.tailObjective_eq_switchValue {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (hj : 0 < j) (hjn : j < n) :
    tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) = switchValue n j γ := by
  obtain ⟨ha, hb⟩ := h.eq_switchPair hj hjn
  rw [ha, hb]
  exact tailObjective_switchPair hj hjn (by linarith [h.2.1, h.2.2.2.1])
    (by linarith [h.1, h.2.2.1, h.2.2.2.1])

/-- The benchmark at total gap `nγ` is the central switching value. -/
theorem benchmark_mul_gap {n : ℕ} (hn : 0 < n) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    benchmark n (n * γ) = switchValue n (n / 2) γ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [benchmark_eq_switchValue (mul_pos hn0 hγ0) (by nlinarith)]
  congr 1
  field_simp

/-- Every feasible homogeneous pair lies above the central switch. -/
theorem switchValue_le_homogeneousObjective {n : ℕ} (hn : 2 ≤ n) {γ b : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : b ∈ Set.Icc 0 (1 - γ)) :
    switchValue n (n / 2) γ ≤ homogeneousObjective n γ b := by
  obtain ⟨j, c, hj, hjn, hs, hmin⟩ := exists_homogeneous_minimizing_switch hn hγ0 hγ1
  have heq : homogeneousObjective n γ c = switchValue n j γ :=
    hs.tailObjective_eq_switchValue (by omega) hjn
  exact (switchValue_central_le (by omega) hjn hγ0 hγ1).trans (heq ▸ hmin hb)

/-- Equality in the homogeneous minimum occurs exactly at the central switch
or its reflection. This includes the even-dimensional coincidence. -/
theorem homogeneousObjective_eq_central_iff {n : ℕ} (hn : 2 ≤ n) {γ b : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : b ∈ Set.Icc 0 (1 - γ)) :
    homogeneousObjective n γ b = switchValue n (n / 2) γ ↔
      IsSwitch n (n / 2) γ (b + γ) b ∨
      IsSwitch n (n - n / 2) γ (b + γ) b := by
  constructor
  · intro heq
    have hmin : IsMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) b := by
      intro c hc
      rw [heq]
      exact switchValue_le_homogeneousObjective hn hγ0 hγ1 hc
    obtain ⟨j, hj, hjn, hs⟩ := homogeneous_minimizer_is_switch hn hγ0 hγ1 hb hmin
    have hval := hs.tailObjective_eq_switchValue (by omega) hjn
    have hindex := (switchValue_eq_central_iff (by omega) hjn hγ0 hγ1).mp
      (hval.symm.trans heq)
    rcases hindex with rfl | rfl
    · exact Or.inl hs
    · exact Or.inr hs
  · rintro (hs | hs)
    · exact hs.tailObjective_eq_switchValue (by omega) (by omega)
    · exact (hs.tailObjective_eq_switchValue (by omega) (by omega)).trans
        ((switchValue_eq_central_iff (by omega : 0 < n - n / 2)
          (by omega) hγ0 hγ1).mpr (Or.inr rfl))

/-- Manuscript homogeneous comparison, including both gap endpoints. -/
theorem homogeneous_minimum {n : ℕ} (hn : 2 ≤ n) {a b : ℝ}
    (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    benchmark n (n * (a - b)) ≤ tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) := by
  have hγ0 : 0 ≤ a - b := sub_nonneg.mpr hba
  have hγ1 : a - b ≤ 1 := by linarith
  rcases hγ0.eq_or_lt with hz | hpos
  · have hab : a = b := by linarith
    subst a
    simp [benchmark]
  rcases hγ1.eq_or_lt with hone | hlt
  · have ha : a = 1 := by linarith
    have hb : b = 0 := by linarith
    subst a b
    simp only [sub_zero, mul_one, benchmark_at_dimension (show 0 < n by omega),
      tailObjective_const_one_zero (show 0 < n by omega), le_refl]
  · rw [benchmark_mul_gap (show 0 < n by omega) hpos hlt]
    have hh := switchValue_le_homogeneousObjective hn hpos hlt
      (show b ∈ Set.Icc 0 (1 - (a - b)) from ⟨hb0, by linarith⟩)
    simpa only [homogeneousObjective, add_sub_cancel] using hh

/-- Exact equality classification for an interior homogeneous gap. -/
theorem homogeneous_minimum_eq_iff {n : ℕ} (hn : 2 ≤ n) {a b : ℝ}
    (hb0 : 0 ≤ b) (ha1 : a ≤ 1) (hgap0 : 0 < a - b) (hgap1 : a - b < 1) :
    tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) = benchmark n (n * (a - b)) ↔
      IsSwitch n (n / 2) (a - b) a b ∨ IsSwitch n (n - n / 2) (a - b) a b := by
  rw [benchmark_mul_gap (show 0 < n by omega) hgap0 hgap1]
  have hh := homogeneousObjective_eq_central_iff hn hgap0 hgap1
    (show b ∈ Set.Icc 0 (1 - (a - b)) from ⟨hb0, by linarith⟩)
  simpa only [homogeneousObjective, add_sub_cancel] using hh

end

end PoissonBinomialComparison
