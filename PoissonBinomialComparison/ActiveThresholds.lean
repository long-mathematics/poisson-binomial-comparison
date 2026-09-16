import PoissonBinomialComparison.LikelihoodRatio
import PoissonBinomialComparison.Endpoints

/-!
# Maximizing thresholds

For a positive mean gap and objective below one, the maximizing thresholds
consist of either one threshold or two consecutive thresholds. The argument
retains deterministic coordinates and possible zero count masses.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

/-- The exact set of thresholds attaining the manuscript's tail objective. -/
def activeThresholds (p q : Fin n → ℝ) : Finset ℕ :=
  (Icc 1 n).filter (fun k ↦ tailDiff p q k = tailObjective p q)

theorem mem_activeThresholds (p q : Fin n → ℝ) (k : ℕ) :
    k ∈ activeThresholds p q ↔
      1 ≤ k ∧ k ≤ n ∧ tailDiff p q k = tailObjective p q := by
  simp only [activeThresholds, mem_filter, mem_Icc]
  tauto

theorem activeThresholds_nonempty (p q : Fin n → ℝ) (hn : 0 < n) :
    (activeThresholds p q).Nonempty := by
  obtain ⟨k, hk, heq⟩ := tailObjective_attained p q hn
  exact ⟨k, mem_filter.mpr ⟨hk, heq.symm⟩⟩

/-- Positive mean gap means some coordinate increases strictly. -/
theorem exists_strict_coordinate_of_meanGap_pos (h : AdmissiblePair p q)
    (hgap : 0 < meanGap p q) : ∃ i, q i < p i := by
  rw [meanGap_eq_sum] at hgap
  obtain ⟨i, _, hi⟩ := (sum_pos_iff_of_nonneg
    (fun i (_ : i ∈ (univ : Finset (Fin n))) ↦ sub_nonneg.mpr (h.2.2 i))).mp hgap
  exact ⟨i, sub_pos.mp hi⟩

/-- The tail-sum identity forces a positive objective for positive mean gap. -/
theorem tailObjective_pos_of_meanGap_pos (hgap : 0 < meanGap p q) :
    0 < tailObjective p q := by
  by_contra hnot
  have hsum : ∑ k ∈ Icc 1 n, tailDiff p q k ≤ 0 := by
    apply sum_nonpos
    intro k hk
    exact (tailDiff_le_tailObjective p q hk).trans (le_of_not_gt hnot)
  rw [sum_tailDiff] at hsum
  exact not_lt_of_ge hsum hgap

/-- The adjacent tail-difference increment is the difference of count masses. -/
theorem tailDiff_sub_succ (p q : Fin n → ℝ) (k : ℕ) :
    tailDiff p q k - tailDiff p q (k + 1) = pbMass p k - pbMass q k := by
  have hp := pbTail_sub_succ p k
  have hq := pbTail_sub_succ q k
  unfold tailDiff
  linarith

/-- Strict adjacent LR inequalities extend to any two distinct counts in the
overlapping positive support. -/
theorem pbMass_strict_likelihoodRatio (h : AdmissiblePair p q)
    (hstrict : ∃ i, q i < p i) {i j : ℕ} (hij : i < j)
    (hq0 : 0 < pbMass q i) (hq1 : 0 < pbMass q j) (hp1 : 0 < pbMass p j) :
    pbMass p i * pbMass q j < pbMass p j * pbMass q i := by
  by_cases hp0 : 0 < pbMass p i
  · have hqm : 0 < pbMass q (i + 1) :=
      pbMass_positive_between h.2.1 (by omega) (by omega) hq0 hq1
    have hpm : 0 < pbMass p (i + 1) := pos_of_mul_pos_left
      ((mul_pos hp0 hqm).trans_le (pbMass_likelihoodRatio h i (i + 1) (by omega)))
      (pbMass_nonneg h.2.1 i)
    have hs := pbMass_strict_adjacent_likelihoodRatio h hstrict i hq0 hqm hpm
    have hw := pbMass_likelihoodRatio h (i + 1) j (by omega)
    apply (mul_lt_mul_iff_right₀ hqm).mp
    have h1 := mul_lt_mul_of_pos_right hs hq1
    have h2 := mul_le_mul_of_nonneg_right hw hq0.le
    nlinarith
  · have hz : pbMass p i = 0 := le_antisymm (le_of_not_gt hp0) (pbMass_nonneg h.1 i)
    rw [hz, zero_mul]
    exact mul_pos hp1 hq0

/-- If every lower count has zero mass, the upper tail is one. -/
theorem pbTail_eq_one_of_mass_zero_below (p : Fin n → ℝ) (k : ℕ)
    (hz : ∀ j < k, pbMass p j = 0) : pbTail p k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (fun j hj ↦ hz j (by omega))
    have hdiff := pbTail_sub_succ p k
    rw [hz k (by omega), hprev] at hdiff
    linarith

/-- A missing count splits an interval-supported Bernoulli law completely to
one side: its upper tail is either zero or one. -/
theorem pbTail_eq_zero_or_one_of_mass_zero (hp : ValidParameters p) (k : ℕ)
    (hz : pbMass p k = 0) : pbTail p k = 0 ∨ pbTail p k = 1 := by
  by_cases hbelow : ∃ j < k, 0 < pbMass p j
  · obtain ⟨j, hj, hpj⟩ := hbelow
    left
    rw [pbTail_eq_sum_mass]
    apply sum_eq_zero
    intro l hl
    have hkl := (mem_Icc.mp hl).1
    apply le_antisymm _ (pbMass_nonneg hp l)
    by_contra hnot
    have hpk := pbMass_positive_between hp hj.le hkl hpj (lt_of_not_ge hnot)
    rw [hz] at hpk
    exact lt_irrefl _ hpk
  · right
    apply pbTail_eq_one_of_mass_zero_below
    intro j hj
    apply le_antisymm _ (pbMass_nonneg hp j)
    exact le_of_not_gt (fun hpos ↦ hbelow ⟨j, hj, hpos⟩)

/-- A tail difference strictly between zero and one cannot sit at a common
zero count mass. -/
theorem mass_pair_pos_of_tailDiff_between (h : AdmissiblePair p q) (k : ℕ)
    (h0 : 0 < tailDiff p q k) (h1 : tailDiff p q k < 1) :
    0 < pbMass p k ∨ 0 < pbMass q k := by
  by_contra hnot
  push Not at hnot
  have hpz := le_antisymm hnot.1 (pbMass_nonneg h.1 k)
  have hqz := le_antisymm hnot.2 (pbMass_nonneg h.2.1 k)
  rcases pbTail_eq_zero_or_one_of_mass_zero h.1 k hpz with hp | hp <;>
    rcases pbTail_eq_zero_or_one_of_mass_zero h.2.1 k hqz with hq | hq <;>
    simp only [tailDiff, hp, hq] at h0 h1 <;> norm_num at *

/-- The same exclusion holds immediately below a nontrivial tail difference. -/
theorem mass_pair_pos_of_succ_tailDiff_between (h : AdmissiblePair p q) (k : ℕ)
    (h0 : 0 < tailDiff p q (k + 1)) (h1 : tailDiff p q (k + 1) < 1) :
    0 < pbMass p k ∨ 0 < pbMass q k := by
  by_contra hnot
  push Not at hnot
  have hpz := le_antisymm hnot.1 (pbMass_nonneg h.1 k)
  have hqz := le_antisymm hnot.2 (pbMass_nonneg h.2.1 k)
  have heq : tailDiff p q k = tailDiff p q (k + 1) := by
    have hd := tailDiff_sub_succ p q k
    rw [hpz, hqz] at hd
    linarith
  rcases mass_pair_pos_of_tailDiff_between h k (by rwa [heq]) (by rwa [heq]) with hp | hq
  · exact not_lt_of_ge hnot.1 hp
  · exact not_lt_of_ge hnot.2 hq

/-- Two maximizing thresholds can differ by at most one for a positive gap
and objective below one. No strict-interiority assumption on parameters is needed. -/
theorem activeThresholds_distance_le_one (h : AdmissiblePair p q)
    (hgap : 0 < meanGap p q) (hT : tailObjective p q < 1)
    {k l : ℕ} (hk : k ∈ activeThresholds p q) (hl : l ∈ activeThresholds p q) :
    l ≤ k + 1 := by
  by_contra hfar
  have hk' := (mem_activeThresholds p q k).mp hk
  have hl' := (mem_activeThresholds p q l).mp hl
  have hpos := tailObjective_pos_of_meanGap_pos hgap
  have hstrict := exists_strict_coordinate_of_meanGap_pos h hgap
  have hkstep : k + 1 ∈ Icc 1 n := mem_Icc.mpr ⟨by omega, by omega⟩
  have hlstep : l - 1 ∈ Icc 1 n := mem_Icc.mpr ⟨by omega, by omega⟩
  have hlpred : l - 1 + 1 = l := by omega
  have hleft : pbMass q k ≤ pbMass p k := by
    have hb := tailDiff_le_tailObjective p q hkstep
    have hd := tailDiff_sub_succ p q k
    rw [hk'.2.2] at hd
    linarith
  have hright : pbMass p (l - 1) ≤ pbMass q (l - 1) := by
    have hb := tailDiff_le_tailObjective p q hlstep
    have hd := tailDiff_sub_succ p q (l - 1)
    rw [hlpred, hl'.2.2] at hd
    linarith
  have hpk : 0 < pbMass p k := by
    rcases mass_pair_pos_of_tailDiff_between h k (by rwa [hk'.2.2])
      (by rwa [hk'.2.2]) with hp | hq
    · exact hp
    · exact hq.trans_le hleft
  have hql : 0 < pbMass q (l - 1) := by
    rcases mass_pair_pos_of_succ_tailDiff_between h (l - 1)
      (by rwa [hlpred, hl'.2.2]) (by rwa [hlpred, hl'.2.2]) with hp | hq
    · exact hp.trans_le hright
    · exact hq
  have hw := pbMass_likelihoodRatio h k (l - 1) (by omega)
  have hprod := (mul_pos hpk hql).trans_le hw
  have hpl := pos_of_mul_pos_left hprod (pbMass_nonneg h.2.1 k)
  have hqk := pos_of_mul_pos_right hprod (pbMass_nonneg h.1 (l - 1))
  have hs := pbMass_strict_likelihoodRatio h hstrict (by omega : k < l - 1) hqk hql hpl
  have hreverse : pbMass p (l - 1) * pbMass q k ≤ pbMass p k * pbMass q (l - 1) := by
    calc
      pbMass p (l - 1) * pbMass q k ≤ pbMass q (l - 1) * pbMass q k :=
        mul_le_mul_of_nonneg_right hright hqk.le
      _ ≤ pbMass q (l - 1) * pbMass p k := mul_le_mul_of_nonneg_left hleft hql.le
      _ = pbMass p k * pbMass q (l - 1) := mul_comm _ _
  exact not_lt_of_ge hreverse hs

/-- Exact manuscript classification of the maximizing threshold set: a singleton
or two consecutive thresholds, all in the original range `1, ..., n`. -/
theorem activeThresholds_singleton_or_adjacent (h : AdmissiblePair p q)
    (hgap : 0 < meanGap p q) (hT : tailObjective p q < 1) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧
      (activeThresholds p q = {k} ∨
        (k + 1 ≤ n ∧ activeThresholds p q = {k, k + 1})) := by
  obtain ⟨i, _⟩ := exists_strict_coordinate_of_meanGap_pos h hgap
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hne := activeThresholds_nonempty p q hn
  let k := (activeThresholds p q).min' hne
  have hk : k ∈ activeThresholds p q := min'_mem _ hne
  have hk' := (mem_activeThresholds p q k).mp hk
  have hbounds : ∀ l ∈ activeThresholds p q, k ≤ l ∧ l ≤ k + 1 := by
    intro l hl
    have hmin : k ≤ l := min'_le _ l hl
    exact ⟨hmin, activeThresholds_distance_le_one h hgap hT hk hl⟩
  refine ⟨k, hk'.1, hk'.2.1, ?_⟩
  by_cases hnext : k + 1 ∈ activeThresholds p q
  · right
    refine ⟨((mem_activeThresholds p q (k + 1)).mp hnext).2.1, ?_⟩
    ext l
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hl
      have hb := hbounds l hl
      omega
    · rintro (rfl | rfl)
      · exact hk
      · exact hnext
  · left
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨hk, ?_⟩
    intro l hl
    have hb := hbounds l hl
    have hneq : l ≠ k + 1 := by
      intro heq
      exact hnext (heq ▸ hl)
    omega

end

end PoissonBinomialComparison
