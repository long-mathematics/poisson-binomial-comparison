import PoissonBinomialComparison.GradientPositivity

/-!
# One changing parameter vector is constant

The coefficient signs follow from the scalar KKT inequalities and the exact
coordinate-gradient identity. Strict likelihood-ratio comparison on the common
double deletion, with the randomizing Bernoulli variable adjoined, rules out a
pair on which both parameter vectors differ. The final step is an elementary
finite-set consequence of that pairwise alternative.
-/

namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

private theorem valid_update_insert {p : ι → ℝ} {s : Finset ι} {e : ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    ∀ i ∈ insert e s, 0 ≤ Function.update p e w i ∧ Function.update p e w i ≤ 1 := by
  intro i hi
  by_cases hie : i = e
  · subst i
    simpa using And.intro hw0 hw1
  · rw [Function.update_of_ne hie]
    exact hp i ((mem_insert.mp hi).resolve_left hie)

private theorem order_update_insert {p q : ι → ℝ} {s : Finset ι} {e : ι}
    (hpq : ∀ i ∈ s, q i ≤ p i) (w : ℝ) :
    ∀ i ∈ insert e s, Function.update q e w i ≤ Function.update p e w i := by
  intro i hi
  by_cases hie : i = e
  · subst i
    simp
  · rw [Function.update_of_ne hie, Function.update_of_ne hie]
    exact hpq i ((mem_insert.mp hi).resolve_left hie)

/-- The randomized deletion masses retain likelihood-ratio order, including
randomizing parameters zero and one. -/
theorem randomizedSlopeOn_likelihoodRatio {p q : ι → ℝ} {s : Finset ι} {e : ι}
    (he : e ∉ s) (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1) (hpq : ∀ i ∈ s, q i ≤ p i)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    randomizedSlopeOn p s w a * randomizedSlopeOn q s w b ≤
      randomizedSlopeOn p s w b * randomizedSlopeOn q s w a := by
  have h := pbMassIntOn_likelihoodRatio (insert e s)
    (valid_update_insert hq hw0 hw1) (valid_update_insert hp hw0 hw1)
    (order_update_insert hpq w) (a : ℤ) (b : ℤ) (by omega)
  simpa only [pbMassIntOn_natCast, ← randomizedSlopeOn_eq_adjoin p he,
    ← randomizedSlopeOn_eq_adjoin q he] using h

/-- A strict remaining coordinate gives strict adjacent comparison of the
randomized deletion masses wherever the required masses are positive. -/
theorem randomizedSlopeOn_strict_adjacent {p q : ι → ℝ} {s : Finset ι} {e : ι}
    (he : e ∉ s) (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1) (hpq : ∀ i ∈ s, q i ≤ p i)
    (hstrict : ∃ i ∈ s, q i < p i)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (k : ℕ)
    (hq0 : 0 < randomizedSlopeOn q s w k)
    (hq1 : 0 < randomizedSlopeOn q s w (k + 1))
    (hp1 : 0 < randomizedSlopeOn p s w (k + 1)) :
    randomizedSlopeOn p s w k * randomizedSlopeOn q s w (k + 1) <
      randomizedSlopeOn p s w (k + 1) * randomizedSlopeOn q s w k := by
  have hs : ∃ i ∈ insert e s, Function.update q e w i < Function.update p e w i := by
    obtain ⟨i, hi, hqi⟩ := hstrict
    have hie : i ≠ e := by intro hh; subst i; exact he hi
    exact ⟨i, mem_insert_of_mem hi, by simpa [Function.update_of_ne hie] using hqi⟩
  have hc : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
  have h := pbMassIntOn_strict_adjacent (insert e s)
    (valid_update_insert hq hw0 hw1) (valid_update_insert hp hw0 hw1)
    (order_update_insert hpq w) hs (k : ℤ)
    (by simpa only [pbMassIntOn_natCast, ← randomizedSlopeOn_eq_adjoin q he] using hq0)
    (by simpa only [hc, pbMassIntOn_natCast, ← randomizedSlopeOn_eq_adjoin q he] using hq1)
    (by simpa only [hc, pbMassIntOn_natCast, ← randomizedSlopeOn_eq_adjoin p he] using hp1)
  simpa only [hc, pbMassIntOn_natCast, ← randomizedSlopeOn_eq_adjoin p he,
    ← randomizedSlopeOn_eq_adjoin q he] using h

/-- Every randomized finite-law mass is nonnegative for valid parameters. -/
theorem randomizedSlopeOn_nonneg {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (k : ℕ) : 0 ≤ randomizedSlopeOn p s w k := by
  unfold randomizedSlopeOn
  apply add_nonneg (mul_nonneg (sub_nonneg.mpr hw1) (pbMassOn_nonneg hp k))
  apply mul_nonneg hw0
  split
  · exact le_rfl
  · exact pbMassOn_nonneg hp (k - 1)

variable {n : ℕ} {p q : Fin n → ℝ}

/-- Upper-vector KKT conditions force a nonnegative mixed coefficient at every
pair of unequal upper parameters. -/
theorem randomizedMixedCoefficient_nonneg_of_upper_kkt (hp : ValidParameters p)
    {i j : Fin n} {w c : ℝ} {k : ℕ} (hne : p i ≠ p j)
    (hpi : randomizedGradient p w k i ≤ c) (hpj : randomizedGradient p w k j ≤ c)
    (hfi : p i < 1 → randomizedGradient p w k i = c)
    (hfj : p j < 1 → randomizedGradient p w k j = c) :
    0 ≤ randomizedMixedCoefficient p w k i j := by
  have hij : i ≠ j := fun heq ↦ hne (congrArg p heq)
  have hd := randomizedGradient_sub p hij w k
  rcases lt_or_gt_of_ne hne with hijp | hjip
  · have heq := hfi (hijp.trans_le (hp j).2)
    have hprod : 0 ≤ (p j - p i) * randomizedMixedCoefficient p w k i j := by linarith
    exact nonneg_of_mul_nonneg_right hprod (sub_pos.mpr hijp)
  · have heq := hfj (hjip.trans_le (hp i).2)
    have hprod : 0 ≤ (p i - p j) * randomizedMixedCoefficient p w k i j := by nlinarith
    exact nonneg_of_mul_nonneg_right hprod (sub_pos.mpr hjip)

/-- Lower-vector KKT conditions force a nonpositive mixed coefficient at every
pair of unequal lower parameters. -/
theorem randomizedMixedCoefficient_nonpos_of_lower_kkt (hq : ValidParameters q)
    {i j : Fin n} {w c : ℝ} {k : ℕ} (hne : q i ≠ q j)
    (hqi : randomizedGradient q w k i ≤ c) (hqj : randomizedGradient q w k j ≤ c)
    (hfi : 0 < q i → randomizedGradient q w k i = c)
    (hfj : 0 < q j → randomizedGradient q w k j = c) :
    randomizedMixedCoefficient q w k i j ≤ 0 := by
  have hij : i ≠ j := fun heq ↦ hne (congrArg q heq)
  have hd := randomizedGradient_sub q hij w k
  rcases lt_or_gt_of_ne hne with hijq | hjiq
  · have heq := hfj ((hq i).1.trans_lt hijq)
    have hprod : (q j - q i) * randomizedMixedCoefficient q w k i j ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right hprod (sub_pos.mpr hijq)
  · have heq := hfi ((hq j).1.trans_lt hjiq)
    have hprod : (q i - q j) * randomizedMixedCoefficient q w k i j ≤ 0 := by nlinarith
    exact nonpos_of_mul_nonpos_right hprod (sub_pos.mpr hjiq)

/-- A coordinate gradient is the affine mixture of its common double-deletion
masses, with the other coordinate as the mixing parameter. -/
theorem randomizedGradient_eq_double_delete (p : Fin n → ℝ) {i j : Fin n}
    (hij : i ≠ j) (w : ℝ) (k : ℕ) :
    randomizedGradient p w k i =
      randomizedSlopeOn p ((univ.erase i).erase j) w k +
        p j * randomizedMixedCoefficient p w k i j := by
  have hs : insert j ((univ.erase i).erase j) = univ.erase i := by
    apply insert_erase
    simp [hij.symm]
  simpa only [hs, randomizedGradient, randomizedMixedCoefficient] using
    randomizedSlopeOn_insert p (notMem_erase j (univ.erase i)) w k

/-- With a further strict coordinate, scalar KKT conditions exclude a pair
on which both parameter vectors differ. -/
theorem pair_eq_or_eq_of_kkt (h : AdmissiblePair p q) {w c : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k)
    {i j : Fin n} (hstrict : ∃ t, t ≠ i ∧ t ≠ j ∧ q t < p t)
    (hpi : randomizedGradient p w k i ≤ c) (hpj : randomizedGradient p w k j ≤ c)
    (hq_i : randomizedGradient q w k i ≤ c) (hq_j : randomizedGradient q w k j ≤ c)
    (hfpi : p i < 1 → randomizedGradient p w k i = c)
    (hfpj : p j < 1 → randomizedGradient p w k j = c)
    (hfqi : 0 < q i → randomizedGradient q w k i = c)
    (hfqj : 0 < q j → randomizedGradient q w k j = c) :
    p i = p j ∨ q i = q j := by
  by_contra hnot
  push Not at hnot
  have hij : i ≠ j := fun heq ↦ hnot.1 (congrArg p heq)
  let s := ((univ : Finset (Fin n)).erase i).erase j
  let Ap := randomizedSlopeOn p s w (k - 1)
  let Bp := randomizedSlopeOn p s w k
  let Aq := randomizedSlopeOn q s w (k - 1)
  let Bq := randomizedSlopeOn q s w k
  have hCp := randomizedMixedCoefficient_nonneg_of_upper_kkt h.1 hnot.1 hpi hpj hfpi hfpj
  have hCq := randomizedMixedCoefficient_nonpos_of_lower_kkt h.2.1 hnot.2 hq_i hq_j hfqi hfqj
  have hcp : randomizedMixedCoefficient p w k i j = Ap - Bp := by
    simp [randomizedMixedCoefficient, randomizedCoefficientOn, show k ≠ 0 by omega, Ap, Bp, s]
  have hcq : randomizedMixedCoefficient q w k i j = Aq - Bq := by
    simp [randomizedMixedCoefficient, randomizedCoefficientOn, show k ≠ 0 by omega, Aq, Bq, s]
  rw [hcp] at hCp
  rw [hcq] at hCq
  have hswap : ((univ : Finset (Fin n)).erase j).erase i = s := by
    exact erase_right_comm
  have hGi := randomizedGradient_eq_double_delete p hij w k
  have hGj := randomizedGradient_eq_double_delete p hij.symm w k
  have hQi := randomizedGradient_eq_double_delete q hij w k
  have hQj := randomizedGradient_eq_double_delete q hij.symm w k
  rw [hcp] at hGi
  rw [hcq] at hQi
  have hcp' : randomizedMixedCoefficient p w k j i = Ap - Bp := by
    simpa only [randomizedMixedCoefficient, hswap] using hcp
  have hcq' : randomizedMixedCoefficient q w k j i = Aq - Bq := by
    simpa only [randomizedMixedCoefficient, hswap] using hcq
  rw [hcp', hswap] at hGj
  rw [hcq', hswap] at hQj
  change randomizedGradient p w k i = Bp + p j * (Ap - Bp) at hGi
  change randomizedGradient p w k j = Bp + p i * (Ap - Bp) at hGj
  change randomizedGradient q w k i = Bq + q j * (Aq - Bq) at hQi
  change randomizedGradient q w k j = Bq + q i * (Aq - Bq) at hQj
  have hAp : 0 < Ap := by
    have hbound_i : randomizedGradient p w k i ≤ Ap := by
      have hh := mul_nonneg (sub_nonneg.mpr (h.1 j).2) hCp
      nlinarith
    have hbound_j : randomizedGradient p w k j ≤ Ap := by
      have hh := mul_nonneg (sub_nonneg.mpr (h.1 i).2) hCp
      nlinarith
    rcases lt_or_gt_of_ne hnot.1 with hpij | hpji
    · rw [hfpi (hpij.trans_le (h.1 j).2)] at hbound_i
      exact hc.trans_le hbound_i
    · rw [hfpj (hpji.trans_le (h.1 i).2)] at hbound_j
      exact hc.trans_le hbound_j
  have hBq : 0 < Bq := by
    have hbound_i : randomizedGradient q w k i ≤ Bq := by
      have hh := mul_nonpos_of_nonneg_of_nonpos (h.2.1 j).1 hCq
      linarith
    have hbound_j : randomizedGradient q w k j ≤ Bq := by
      have hh := mul_nonpos_of_nonneg_of_nonpos (h.2.1 i).1 hCq
      linarith
    rcases lt_or_gt_of_ne hnot.2 with hqij | hqji
    · rw [hfqj ((h.2.1 i).1.trans_lt hqij)] at hbound_j
      exact hc.trans_le hbound_j
    · rw [hfqi ((h.2.1 j).1.trans_lt hqji)] at hbound_i
      exact hc.trans_le hbound_i
  have hps : ∀ t ∈ s, 0 ≤ p t ∧ p t ≤ 1 := fun t _ ↦ h.1 t
  have hqs : ∀ t ∈ s, 0 ≤ q t ∧ q t ≤ 1 := fun t _ ↦ h.2.1 t
  have hpqs : ∀ t ∈ s, q t ≤ p t := fun t _ ↦ h.2.2 t
  have hie : i ∉ s := by simp [s]
  have hweak : Ap * Bq ≤ Bp * Aq :=
    randomizedSlopeOn_likelihoodRatio hie hps hqs hpqs hw0 hw1 (by omega)
  have hBpnonneg : 0 ≤ Bp := randomizedSlopeOn_nonneg hps hw0 hw1 k
  have hAqnonneg : 0 ≤ Aq := randomizedSlopeOn_nonneg hqs hw0 hw1 (k - 1)
  have hproduct : 0 < Bp * Aq := (mul_pos hAp hBq).trans_le hweak
  have hBp : 0 < Bp := pos_of_mul_pos_left hproduct hAqnonneg
  have hAq : 0 < Aq := pos_of_mul_pos_right hproduct hBpnonneg
  have hs : ∃ t ∈ s, q t < p t := by
    obtain ⟨t, hti, htj, ht⟩ := hstrict
    exact ⟨t, by simp [s, hti, htj], ht⟩
  have hpred : k - 1 + 1 = k := by omega
  have hlt : Ap * Bq < Bp * Aq := by
    have hh := randomizedSlopeOn_strict_adjacent hie hps hqs hpqs hs hw0 hw1 (k - 1)
      hAq (by simpa only [hpred] using hBq) (by simpa only [hpred] using hBp)
    simpa only [hpred] using hh
  have hreverse : Bp * Aq ≤ Ap * Bq := by
    calc
      Bp * Aq ≤ Ap * Aq := mul_le_mul_of_nonneg_right (by linarith) hAq.le
      _ ≤ Ap * Bq := mul_le_mul_of_nonneg_left (by linarith) hAp.le
  exact not_lt_of_ge hreverse hlt

/-- A pairwise equality alternative forces one of the two vectors to be
constant on the coordinate set. This purely finite argument has no KKT hypotheses. -/
theorem constant_on_or_constant_on_of_pairwise {α : Type*} (s : Finset α)
    (f g : α → ℝ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, f i = f j ∨ g i = g j) :
    (∃ a, ∀ i ∈ s, f i = a) ∨ (∃ b, ∀ i ∈ s, g i = b) := by
  by_cases hf : ∀ i ∈ s, ∀ j ∈ s, f i = f j
  · left
    by_cases hs : s.Nonempty
    · obtain ⟨j, hj⟩ := hs
      exact ⟨f j, fun i hi ↦ hf i hi j hj⟩
    · exact ⟨0, fun i hi ↦ False.elim (hs ⟨i, hi⟩)⟩
  · push Not at hf
    obtain ⟨i, hi, j, hj, hij⟩ := hf
    have hgij : g i = g j := (hpair i hi j hj).resolve_left hij
    right
    refine ⟨g i, ?_⟩
    intro t ht
    by_cases hti : f t = f i
    · have htj : f t ≠ f j := by intro heq; exact hij (hti.symm.trans heq)
      exact ((hpair t ht j hj).resolve_left htj).trans hgij.symm
    · exact (hpair t ht i hi).resolve_left hti

/-- On any set of at least three changing coordinates, the scalar KKT
conditions and positive multiplier force one parameter vector to be constant
(ONECONST). -/
theorem exists_constant_vector_of_kkt (h : AdmissiblePair p q) {I : Finset (Fin n)}
    (hcard : 3 ≤ I.card) (hchanging : ∀ i ∈ I, q i < p i)
    {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k)
    (hupper : ∀ i ∈ I, randomizedGradient p w k i ≤ c ∧
      (p i < 1 → randomizedGradient p w k i = c))
    (hlower : ∀ i ∈ I, randomizedGradient q w k i ≤ c ∧
      (0 < q i → randomizedGradient q w k i = c)) :
    (∃ a, ∀ i ∈ I, p i = a) ∨ (∃ b, ∀ i ∈ I, q i = b) := by
  apply constant_on_or_constant_on_of_pairwise I p q
  intro i hi j hj
  have hpaircard : ({i, j} : Finset (Fin n)).card < I.card := by
    have hle := card_insert_le i ({j} : Finset (Fin n))
    simp only [card_singleton] at hle
    omega
  obtain ⟨t, ht, htpair⟩ := exists_mem_notMem_of_card_lt_card hpaircard
  have hti : t ≠ i := by intro heq; subst t; exact htpair (by simp)
  have htj : t ≠ j := by intro heq; subst t; exact htpair (by simp)
  exact pair_eq_or_eq_of_kkt h hw0 hw1 hc hk
    ⟨t, hti, htj, hchanging t ht⟩
    (hupper i hi).1 (hupper j hj).1 (hlower i hi).1 (hlower j hj).1
    (hupper i hi).2 (hupper j hj).2 (hlower i hi).2 (hlower j hj).2

end

end PoissonBinomialComparison
