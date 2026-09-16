import PoissonBinomialComparison.Adjoining
import PoissonBinomialComparison.CommonStationarity
import PoissonBinomialComparison.Reflection
import PoissonBinomialComparison.DeletionMixture

/-!
# Excluding an all-one changing upper block

After complementing successes, the upper changing block is deterministic zero.
The endpoint gradient inequality says that the reflected common law is on the
increasing side of its mass sequence. Adjoining two positive failure parameters
strictly decreases that mass, contradicting the active mass tie. This finite
argument proves the same strict comparison as the manuscript's path argument.
-/

namespace PoissonBinomialComparison

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- Adding coordinates whose parameters are zero leaves every integer-indexed mass unchanged. -/
theorem pbMassIntOn_union_zero_parameters (p : ι → ℝ) (s t : Finset ι)
    (hz : ∀ i ∈ t, i ∉ s → p i = 0) (k : ℤ) :
    pbMassIntOn p (s ∪ t) k = pbMassIntOn p s k := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    have hz' : ∀ j ∈ t, j ∉ s → p j = 0 := fun j hj => hz j (mem_insert_of_mem hj)
    rw [union_insert]
    by_cases him : i ∈ s ∪ t
    · rw [insert_eq_of_mem him, ih hz']
    · rw [pbMassIntOn_insert p him, hz i (mem_insert_self i t)
        (fun hs => him (mem_union_left t hs))]
      simpa using ih hz'

/-- Two positive additions strictly decrease a positive mass on its increasing side. -/
theorem pbMassIntOn_univ_lt_of_two_positive {n : ℕ} {p : Fin n → ℝ}
    (hp : ValidParameters p) (s : Finset (Fin n)) {i j : Fin n}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j)
    (hpi : 0 < p i) (hpj : 0 < p j) (k : ℤ)
    (hk : 0 < pbMassIntOn p s k)
    (hadj : pbMassIntOn p s (k-1) ≤ pbMassIntOn p s k) :
    pbMassIntOn p univ k < pbMassIntOn p s k := by
  have hU (t : Finset (Fin n)) : t ∪ univ = univ := union_eq_right.mpr (subset_univ t)
  rcases hadj.eq_or_lt with heq | hlt
  · simpa only [hU] using pbMassIntOn_union_lt_of_two_positive_of_tie s univ hi hj hij
      (fun l _ => hp l) hpi hpj k hk heq
  · have hstrict := pbMassIntOn_insert_lt hi hpi k hlt
    have hprefix := (pbMassIntOn_cross s (fun l _ => hp l)).prefix_order
      (pbMassIntOn_nonneg (fun l _ => hp l)) hk hadj
    have hprefix' := pbMassIntOn_insert_prefix_order hi (hp i) k hprefix
    have hle := (pbMassIntOn_union_prefix_order (insert i s) univ
      (fun l _ => hp l) k hprefix').1
    simp only [hU] at hle
    exact hle.trans_lt hstrict

/-- If an upper block is all one and the upper mass is on its decreasing side,
any lower block differing in at least two coordinates has strictly smaller mass. -/
theorem pbMass_lt_of_upper_one_block {n k : ℕ} {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hk : k < n) (s : Finset (Fin n))
    (hcommon : ∀ i ∈ s, p i = q i) (hone : ∀ i ∉ s, p i = 1)
    {i j : Fin n} (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j)
    (hqi : q i < 1) (hqj : q j < 1) (hpos : 0 < pbMass p k)
    (hadj : pbMass p (k+1) ≤ pbMass p k) : pbMass q k < pbMass p k := by
  let P : Fin n → ℝ := fun l => 1-p l
  let Q : Fin n → ℝ := fun l => 1-q l
  have hQ : ValidParameters Q := fun l => ⟨sub_nonneg.mpr (h.2.1 l).2,
    by dsimp [Q]; linarith [(h.2.1 l).1]⟩
  have hbase (z : ℤ) : pbMassIntOn Q s z = pbMassIntOn P univ z := by
    rw [pbMassIntOn_congr (q := P) (fun l hl => by dsimp [P,Q]; rw [hcommon l hl])]
    have hz : ∀ l ∈ (univ : Finset (Fin n)), l ∉ s → P l = 0 := by
      intro l _ hl
      simp [P,hone l hl]
    simpa only [union_eq_right.mpr (subset_univ s)] using (pbMassIntOn_union_zero_parameters P s univ hz z).symm
  have href (l : ℕ) (hl : l ≤ n) : pbMassIntOn P univ (n-l : ℕ) = pbMass p l := by
    simp only [pbMassIntOn_natCast]
    change pbMass (fun l => 1-p l) (n-l) = _
    rw [pbMass_complement p (n-l) (by omega), Nat.sub_sub_self hl]
  have hcount : ((n-k : ℕ) : ℤ)-1 = ((n-(k+1) : ℕ) : ℤ) := by omega
  have hbasepos : 0 < pbMassIntOn Q s (n-k : ℕ) := by rw [hbase,href k hk.le]; exact hpos
  have hbaseadj : pbMassIntOn Q s (((n-k : ℕ) : ℤ)-1) ≤ pbMassIntOn Q s (n-k : ℕ) := by
    rw [hcount,hbase,hbase,href (k+1) (by omega),href k hk.le]
    exact hadj
  have hlt := pbMassIntOn_univ_lt_of_two_positive hQ s hi hj hij
    (show 0 < Q i from sub_pos.mpr hqi) (show 0 < Q j from sub_pos.mpr hqj)
    (n-k : ℕ) hbasepos hbaseadj
  rw [hbase,href k hk.le,pbMassIntOn_natCast] at hlt
  change pbMass (fun l => 1-q l) (n-k) < _ at hlt
  rwa [pbMass_complement q (n-k) (by omega),Nat.sub_sub_self hk.le] at hlt

/-- At an upper deterministic coordinate, the randomized gradient combines
adjacent masses of the full law. -/
theorem randomizedGradient_of_parameter_one {n k : ℕ} {p : Fin n → ℝ}
    (hk : 1 ≤ k) (j : Fin n) (hj : p j = 1) (w : ℝ) :
    randomizedGradient p w k j = w * pbMass p k + (1-w) * pbMass p (k+1) := by
  have h0 := pbMass_delete_succ p j (k-1)
  have h1 := pbMass_delete_succ p j k
  simp only [hj, sub_self, zero_mul, one_mul, zero_add, show k-1+1 = k by omega] at h0 h1
  simp only [randomizedGradient,randomizedSlopeOn,show k ≠ 0 by omega,ite_false]
  rw [h0,h1]
  ring

/-- The common-versus-changing gradient inequality gives the upper adjacent-mass order. -/
theorem upper_adjacent_le_of_gradient_order {n k : ℕ} {p : Fin n → ℝ}
    (hk : 1 ≤ k) {w : ℝ} (hw : w < 1) (i j : Fin n)
    (hi : p i = w) (hj : p j = 1)
    (hgrad : randomizedGradient p w k j ≤ randomizedGradient p w k i) :
    pbMass p (k+1) ≤ pbMass p k := by
  rw [randomizedGradient_eq_mass_of_parameter_eq hk i hi,
    randomizedGradient_of_parameter_one hk j hj] at hgrad
  nlinarith

/-- An active mass tie and the endpoint KKT gradient inequality exclude an
all-one upper changing block. Only two changing coordinates are needed here. -/
theorem upper_one_block_impossible {n k : ℕ} {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hk0 : 1 ≤ k) (hkn : k < n)
    (s : Finset (Fin n)) (hcommon : ∀ i ∈ s, p i = q i)
    (hone : ∀ i ∉ s, p i = 1) {w : ℝ} (hw : w < 1)
    (c i j : Fin n) (hc : p c = w) (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j)
    (hqi : q i < 1) (hqj : q j < 1) (hpos : 0 < pbMass p k)
    (hgrad : randomizedGradient p w k i ≤ randomizedGradient p w k c)
    (htie : pbMass p k = pbMass q k) : False := by
  have hadj := upper_adjacent_le_of_gradient_order hk0 hw c i hc (hone i hi) hgrad
  have hlt := pbMass_lt_of_upper_one_block h hkn s hcommon hone hi hj hij hqi hqj hpos hadj
  rw [htie] at hlt
  exact (lt_irrefl _) hlt

/-- After one changing vector is homogeneous, the upper common value is strictly
below one under the manuscript's active mass and KKT conditions. -/
theorem homogeneous_upper_changing_lt_one {n k : ℕ} {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hk0 : 1 ≤ k) (hkn : k < n)
    (hcard : 2 ≤ (positiveGapCoordinates p q).card) {a w : ℝ} (hw : w < 1)
    (hconst : ∀ i, q i < p i → p i = a)
    (hcommon : ∀ i, p i = q i → p i = w)
    (hnotone : p ≠ (fun _ => 1)) (hpos : 0 < pbMass p k)
    (hgrad : ∀ i c, q i < p i → p c = q c →
      randomizedGradient p w k i ≤ randomizedGradient p w k c)
    (htie : pbMass p k = pbMass q k) : a < 1 := by
  obtain ⟨i,hi,j,hj,hij⟩ := one_lt_card.mp (show 1 < (positiveGapCoordinates p q).card by omega)
  have hi' : q i < p i := (mem_filter.mp hi).2
  have hj' : q j < p j := (mem_filter.mp hj).2
  have ha : a ≤ 1 := by rw [← hconst i hi']; exact (h.1 i).2
  by_contra hlt
  have ha1 : a = 1 := by linarith
  have hex : ∃ c, p c ≠ 1 := by
    by_contra hh
    push Not at hh
    exact hnotone (funext hh)
  obtain ⟨c,hc⟩ := hex
  have hccommon : p c = q c := by
    by_contra hcne
    have hcstrict : q c < p c := lt_of_le_of_ne (h.2.2 c) (Ne.symm hcne)
    exact hc ((hconst c hcstrict).trans ha1)
  let s := (univ : Finset (Fin n)).filter (fun l => p l = q l)
  have hsc : ∀ l ∈ s, p l = q l := fun l hl => (mem_filter.mp hl).2
  have hsone : ∀ l ∉ s, p l = 1 := by
    intro l hl
    have hne : p l ≠ q l := by simpa [s] using hl
    exact (hconst l (lt_of_le_of_ne (h.2.2 l) hne.symm)).trans ha1
  have his : i ∉ s := by simp [s,ne_of_gt hi']
  have hjs : j ∉ s := by simp [s,ne_of_gt hj']
  exact upper_one_block_impossible h hk0 hkn s hsc hsone hw c i j
    (hcommon c hccommon) his hjs hij (by rw [← ha1,← hconst i hi']; exact hi')
    (by rw [← ha1,← hconst j hj']; exact hj') hpos (hgrad i c hi' hccommon) htie

end PoissonBinomialComparison
