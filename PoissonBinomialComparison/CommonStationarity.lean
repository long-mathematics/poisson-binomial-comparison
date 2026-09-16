import PoissonBinomialComparison.TailKKT
import PoissonBinomialComparison.Reindex
import PoissonBinomialComparison.SwitchMaximum

/-!
# Common-coordinate stationarity

An active mass tie and equality of the randomized gradients force a common
interior coordinate to equal the randomizing parameter. Strict likelihood-ratio
order rules out the singular two-equation system, including support endpoints.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Ordered Bernoulli laws with positive opposite extreme masses cannot agree
at two adjacent counts if either common mass is positive. -/
theorem adjacent_mass_equal_impossible {p q : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, q i ≤ p i) (hstrict : ∃ i ∈ s, q i < p i)
    (htop : 0 < pbMassOn p s s.card) (hzero : 0 < pbMassOn q s 0)
    {k : ℕ} (hk : 1 ≤ k) (hks : k ≤ s.card)
    (heq0 : pbMassOn p s (k-1) = pbMassOn q s (k-1))
    (heq1 : pbMassOn p s k = pbMassOn q s k)
    (hpos : 0 < pbMassOn p s (k-1) ∨ 0 < pbMassOn p s k) : False := by
  have hp1 : 0 < pbMassOn p s k := by
    rcases hpos with hprev | hnext
    · exact pbMassOn_positive_between s hp (by omega) hks hprev htop
    · exact hnext
  have hq1 : 0 < pbMassOn q s k := heq1 ▸ hp1
  have hq0 : 0 < pbMassOn q s (k-1) :=
    pbMassOn_positive_between s hq (Nat.zero_le _) (by omega) hzero hq1
  have hcast : ((k-1 : ℕ) : ℤ)+1 = (k : ℤ) := by omega
  have hlr := pbMassIntOn_strict_adjacent s hq hp hpq hstrict ((k-1 : ℕ) : ℤ)
    (by simpa only [pbMassIntOn_natCast] using hq0)
    (by simpa only [hcast,pbMassIntOn_natCast] using hq1)
    (by simpa only [hcast,pbMassIntOn_natCast] using hp1)
  simp only [hcast,pbMassIntOn_natCast,heq0,heq1] at hlr
  nlinarith

variable {n : ℕ} {p q : Fin n → ℝ}

/-- A tied common coordinate equals the randomizing weight (`commonlambda`). -/
theorem common_parameter_eq_weight (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {k : ℕ} (hk0 : 1 ≤ k) (hkn : k < n)
    (htie : pbMass p k = pbMass q k)
    (i : Fin n) (hcommon : p i = q i) (hstrict : ∃ j, j ≠ i ∧ q j < p j)
    (hgrad : randomizedGradient p w k i = randomizedGradient q w k i)
    (hpos : 0 < randomizedGradient p w k i) : p i = w := by
  let s := (univ : Finset (Fin n)).erase i
  have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 := fun j _ ↦ h.1 j
  have hqs : ∀ j ∈ s, 0 ≤ q j ∧ q j ≤ 1 := fun j _ ↦ h.2.1 j
  have hcard : s.card = n-1 := by simp [s]
  have hstrict' : ∃ j ∈ s, q j < p j := by
    obtain ⟨j,hji,hj⟩ := hstrict
    exact ⟨j,by simp [s,hji],hj⟩
  have hpred : k-1+1 = k := by omega
  have hP := pbMass_delete_succ p i (k-1)
  have hQ := pbMass_delete_succ q i (k-1)
  rw [hpred] at hP hQ
  change pbMass p k = (1-p i)*pbMassOn p s k+p i*pbMassOn p s (k-1) at hP
  change pbMass q k = (1-q i)*pbMassOn q s k+q i*pbMassOn q s (k-1) at hQ
  have hG : (1-w)*pbMassOn p s k+w*pbMassOn p s (k-1) =
      (1-w)*pbMassOn q s k+w*pbMassOn q s (k-1) := by
    simpa only [randomizedGradient, randomizedSlopeOn, show k ≠ 0 by omega, ite_false] using hgrad
  have hT : (1-p i)*pbMassOn p s k+p i*pbMassOn p s (k-1) =
      (1-p i)*pbMassOn q s k+p i*pbMassOn q s (k-1) := by
    rw [← hP, hcommon, ← hQ]
    exact htie
  by_contra hneq
  have hdet : p i-w ≠ 0 := sub_ne_zero.mpr hneq
  have h0 : (p i-w)*(pbMassOn p s (k-1)-pbMassOn q s (k-1)) = 0 := by
    linear_combination (1-w)*hT-(1-p i)*hG
  have h1 : (p i-w)*(pbMassOn p s k-pbMassOn q s k) = 0 := by
    linear_combination p i*hG-w*hT
  have heq0 := sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hdet)
  have heq1 := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hdet)
  have hmpos : 0 < pbMassOn p s (k-1) ∨ 0 < pbMassOn p s k := by
    by_contra hnot
    push Not at hnot
    have hnonpos := add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hw1) hnot.2)
      (mul_nonpos_of_nonneg_of_nonpos hw0 hnot.1)
    have hGpos : 0 < (1-w)*pbMassOn p s k+w*pbMassOn p s (k-1) := by
      simpa only [randomizedGradient,randomizedSlopeOn,show k ≠ 0 by omega,ite_false] using hpos
    linarith
  apply adjacent_mass_equal_impossible hps hqs (fun j _ ↦ h.2.2 j) hstrict'
    (by rw [pbMassOn_card_eq_prod]; exact prod_pos (fun j _ ↦ hp j))
    (by rw [pbMassOn_zero]; exact prod_pos (fun j _ ↦ sub_pos.mpr (hq j)))
    hk0 (by omega) heq0 heq1 hmpos

/-- At a common coordinate equal to the randomizing weight, the randomized
gradient is exactly the original tied count mass (`commonf`). -/
theorem randomizedGradient_eq_mass_of_parameter_eq {p : Fin n → ℝ} {w : ℝ}
    {k : ℕ} (hk : 1 ≤ k) (i : Fin n) (hi : p i = w) :
    randomizedGradient p w k i = pbMass p k := by
  have hp := pbMass_delete_succ p i (k-1)
  rw [show k-1+1 = k by omega, hi] at hp
  simpa [randomizedGradient,randomizedSlopeOn,show k ≠ 0 by omega] using hp.symm

/-- Equal positive deletion masses at an active pure threshold make deletion of
the common coordinate preserve the objective, even when it is nondeterministic. -/
theorem exists_deleted_pair_of_stationary_active (h : AdmissiblePair p q)
    (i : Fin n) (hi : p i = q i) {k : ℕ} (hk : k ∈ activeThresholds p q)
    (heq : pbMassOn p (univ.erase i) (k-1) = pbMassOn q (univ.erase i) (k-1))
    (hpos : 0 < pbMassOn q (univ.erase i) (k-1)) :
    ∃ r t : Fin (n-1) → ℝ, AdmissiblePair r t ∧ meanGap r t = meanGap p q ∧
      tailObjective r t = tailObjective p q := by
  let s := (univ : Finset (Fin n)).erase i
  have hcard : s.card = n-1 := by simp [s]
  have hex : ∃ r t : Fin s.card → ℝ, AdmissiblePair r t ∧ meanGap r t = meanGap p q ∧
      tailObjective r t = tailObjective p q := by
    let r := finsetParameters p s
    let t := finsetParameters q s
    have hrs : AdmissiblePair r t := ⟨valid_finsetParameters _ (fun j _ ↦ h.1 j),
      valid_finsetParameters _ (fun j _ ↦ h.2.1 j), fun _ ↦ h.2.2 _⟩
    have hm : pbMass r (k-1) = pbMass t (k-1) := by
      simpa only [r,t,pbMass_finsetParameters] using heq
    have hmp : 0 < pbMass t (k-1) := by
      simpa only [t,pbMass_finsetParameters] using hpos
    have hmax := tailObjective_eq_tailDiff_of_equal_mass hrs (k-1) hm hmp
    have hk' := (mem_activeThresholds p q k).mp hk
    have hpred : k-1+1 = k := by omega
    have hadj := tailDiff_sub_succ r t (k-1)
    rw [hpred,hm,sub_self] at hadj
    have hrec : tailDiff p q k = (1-p i)*tailDiff r t k+p i*tailDiff r t (k-1) := by
      unfold tailDiff
      simp only [r,t,pbTail_finsetParameters]
      have hP := pbTail_delete_succ p i (k-1)
      have hQ := pbTail_delete_succ q i (k-1)
      rw [hpred] at hP hQ
      rw [hP,hQ,← hi]
      dsimp [s]
      ring
    refine ⟨r,t,hrs,?_,?_⟩
    · simp only [r,t,meanGap,sum_finsetParameters]
      have hP := sum_erase_add univ p (mem_univ i)
      have hQ := sum_erase_add univ q (mem_univ i)
      dsimp [s]
      linarith
    · rw [hmax,← hk'.2.2,hrec]
      rw [sub_eq_zero.mp hadj]
      ring
  rwa [hcard] at hex

end

end PoissonBinomialComparison
