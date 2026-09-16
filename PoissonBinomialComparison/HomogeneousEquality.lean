import PoissonBinomialComparison.HomogeneousMinimum

/-!
# Explicit central-switch equality cases

The intrinsic equal-height characterization is equivalent to the canonical
central pair and its reflection. In even dimension the two pairs coincide
and have exactly the complementary formulas in the manuscript.
-/

namespace PoissonBinomialComparison

noncomputable section

/-- Canonical and reflected forms of the homogeneous equality classification. -/
theorem homogeneous_minimum_eq_canonical_iff {n : ℕ} (hn : 2 ≤ n) {a b : ℝ}
    (hb0 : 0 ≤ b) (ha1 : a ≤ 1) (hg0 : 0 < a-b) (hg1 : a-b < 1) :
    tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) = benchmark n (n*(a-b)) ↔
      (a = switchUpper n (n/2) (a-b) ∧ b = switchLower n (n/2) (a-b)) ∨
      (a = 1-switchLower n (n/2) (a-b) ∧ b = 1-switchUpper n (n/2) (a-b)) := by
  rw [homogeneous_minimum_eq_iff hn hb0 ha1 hg0 hg1]
  have hj : 0 < n/2 := by omega
  have hjn : n/2 < n := by omega
  have hr := switchPair_reflection hj hjn hg0 hg1
  constructor
  · rintro (hs | hs)
    · exact Or.inl (hs.eq_switchPair hj hjn)
    · obtain ⟨ha,hb⟩ := hs.eq_switchPair (by omega) (by omega)
      exact Or.inr ⟨ha.trans hr.1,hb.trans hr.2⟩
  · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
    · have hs := switchPair_spec hj hjn hg0 hg1
      rw [← ha,← hb] at hs
      exact Or.inl hs
    · have hs := switchPair_spec (by omega : 0 < n-n/2) (by omega : n-n/2 < n) hg0 hg1
      rw [hr.1,hr.2,← ha,← hb] at hs
      exact Or.inr hs

/-- In even dimension the homogeneous equality cases are exactly the
complementary parameter formulas, with no extra reflected alternative. -/
theorem homogeneous_minimum_even_eq_iff {m : ℕ} (hm : 0 < m) {a b : ℝ}
    (hb0 : 0 ≤ b) (ha1 : a ≤ 1) (hg0 : 0 < a-b) (hg1 : a-b < 1) :
    tailObjective (fun _ : Fin (2*m) ↦ a) (fun _ ↦ b) =
      benchmark (2*m) ((2*m:ℝ)*(a-b)) ↔
      a = (1+(a-b))/2 ∧ b = (1-(a-b))/2 := by
  have hh := homogeneous_minimum_eq_canonical_iff (by omega : 2 ≤ 2*m) hb0 ha1 hg0 hg1
  have he := switchPair_even hm hg0 hg1
  simp only [show 2*m/2=m by omega,he.1,he.2] at hh
  have h1 : 1-(1-(a-b))/2 = (1+(a-b))/2 := by ring
  have h2 : 1-(1+(a-b))/2 = (1-(a-b))/2 := by ring
  simpa only [h1,h2,or_self,Nat.cast_mul,Nat.cast_ofNat] using hh

end

end PoissonBinomialComparison
