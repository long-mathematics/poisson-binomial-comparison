import PoissonBinomialComparison.BlockCoordinates

/-!
# Homogeneity of the lower changing coordinates

The only second-variation input is the explicitly stated conclusion that two
coordinates cannot repeat a smaller positive value below another positive
value. All remaining exclusions are proved from the actual coordinate gradients.
-/

namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

/-- QTWO and QONE exclude two distinct positive lower values once the
second-variation exclusion of a repeated smaller value is available. -/
theorem lower_positive_values_equal_of_no_smaller_repeat
    (hq : ValidParameters q) (I C : Finset (Fin n))
    (hpart : univ = C ∪ I) (hCI : Disjoint C I) (hr : 3 ≤ I.card)
    {w a c : ℝ} (hw : 0 ≤ w ∧ w ≤ 1) (ha : a < 1) (hc : 0 < c) (k : ℕ)
    (hpC : ∀ i ∈ C, p i = w) (hqC : ∀ i ∈ C, q i = w)
    (hpI : ∀ i ∈ I, p i = a) (hqI : ∀ i ∈ I, q i < a)
    (hpgrad : ∀ i ∈ I, randomizedGradient p w k i = c)
    (hqgrad : ∀ i ∈ I, 0 < q i → randomizedGradient q w k i = c)
    (hsmall : ∀ i ∈ I, ∀ j ∈ I, ∀ l ∈ I,
      0 < q i → q i = q j → q i < q l → i = j) :
    ∀ i ∈ I, ∀ j ∈ I, 0 < q i → 0 < q j → q i = q j := by
  classical
  have hexclude : ∀ i ∈ I, ∀ j ∈ I, 0 < q i → q i < q j → False := by
    intro i hi j hj hqi hij
    let H := I.filter (fun l ↦ q l = q j)
    let Z := I.filter (fun l ↦ q l = 0)
    have hqi0 : q i ≠ 0 := hqi.ne'
    have hqj : 0 < q j := hqi.trans hij
    have hvalues : ∀ l ∈ I, q l = 0 ∨ q l = q i ∨ q l = q j := by
      intro l hl
      by_cases hz : q l = 0
      · exact Or.inl hz
      by_cases hui : q l = q i
      · exact Or.inr (Or.inl hui)
      by_cases hvj : q l = q j
      · exact Or.inr (Or.inr hvj)
      have hql : 0 < q l := lt_of_le_of_ne (hq l).1 (Ne.symm hz)
      exact False.elim (not_three_distinct_of_equal_positive_gradients hq hw.1 hw.2 hc k
        hij.ne (Ne.symm hui) (Ne.symm hvj) (hqgrad i hi hqi) (hqgrad j hj hqj) (hqgrad l hl hql))
    have hsmallonly : ∀ l ∈ I, q l = q i → l = i := by
      intro l hl heq
      exact hsmall l hl i hi j hj (by rwa [heq]) heq (by rwa [heq])
    have hI : I = insert i (H ∪ Z) := by
      ext l
      simp only [mem_insert, mem_union, H, Z, mem_filter]
      constructor
      · intro hl
        rcases hvalues l hl with hz | hu | hv
        · exact Or.inr (Or.inr ⟨hl, hz⟩)
        · exact Or.inl (hsmallonly l hl hu)
        · exact Or.inr (Or.inl ⟨hl, hv⟩)
      · rintro (rfl | hl | hl)
        · exact hi
        · exact hl.1
        · exact hl.1
    have hHsub : H ⊆ I := filter_subset _ _
    have hZsub : Z ⊆ I := filter_subset _ _
    have hHZ : Disjoint H Z := by
      apply disjoint_left.mpr
      intro l hlH hlZ
      have hu := (mem_filter.mp hlH).2
      have hz := (mem_filter.mp hlZ).2
      exact hqj.ne' (hu.symm.trans hz)
    have hiC : i ∉ C := fun hic ↦ disjoint_left.mp hCI hic hi
    have hin : i ∉ C ∪ H ∪ Z := by
      simp only [mem_union, not_or]
      exact ⟨⟨hiC, by simp [H, hij.ne]⟩, by simp [Z, hqi0]⟩
    have hcard : I.card = H.card + Z.card + 1 := by
      rw [hI, card_insert_of_notMem (by simp [H, Z, hij.ne, hqi0])]
      rw [card_union_of_disjoint hHZ]
    have hpatt : univ = insert i (C ∪ H ∪ Z) := by
      rw [hpart, hI]
      ext l
      simp only [mem_union, mem_insert]
      tauto
    exact not_two_positive_coordinate_pattern p q C H Z i k hpatt hin
      (hCI.mono_right hHsub) (hCI.mono_right hZsub) hHZ
      ⟨j, by simp [H, hj]⟩ (by omega) hw hqi hij (hqI j hj) ha hc hpC hqC
      (fun l hl ↦ hpI l (by rcases mem_union.mp hl with hl | hl; exact hHsub hl; exact hZsub hl))
      rfl (fun l hl ↦ (mem_filter.mp hl).2) (fun l hl ↦ (mem_filter.mp hl).2)
      (hpgrad i hi) (hqgrad i hi hqi)
      (fun l hl ↦ hqgrad l (hHsub hl) (by rw [(mem_filter.mp hl).2]; exact hqj))
  intro i hi j hj hqi hqj
  rcases lt_trichotomy (q i) (q j) with hij | heq | hji
  · exact False.elim (hexclude i hi j hj hqi hij)
  · exact heq
  · exact False.elim (hexclude j hj i hi hqj hji)

/-- Actual-coordinate classification of the lower changing vector. The sole
conditional input is QSPLIT's exclusion of a repeated smaller positive value;
QTWO, QONE and QZERO are discharged within this theorem. -/
theorem lower_changing_coordinates_constant
    (hq : ValidParameters q) (I C : Finset (Fin n))
    (hpart : univ = C ∪ I) (hCI : Disjoint C I) (hr : 3 ≤ I.card)
    {w a c : ℝ} (hw : 0 ≤ w ∧ w ≤ 1) (ha : a < 1) (hc : 0 < c) (k : ℕ)
    (hpC : ∀ i ∈ C, p i = w) (hqC : ∀ i ∈ C, q i = w)
    (hpI : ∀ i ∈ I, p i = a) (hqI : ∀ i ∈ I, q i < a)
    (hpgrad : ∀ i ∈ I, randomizedGradient p w k i = c)
    (hqgrad : ∀ i ∈ I, 0 < q i → randomizedGradient q w k i = c)
    (hqzero : ∀ i ∈ I, q i = 0 → randomizedGradient q w k i ≤ c)
    (hsmall : ∀ i ∈ I, ∀ j ∈ I, ∀ l ∈ I,
      0 < q i → q i = q j → q i < q l → i = j) :
    ∃ b : ℝ, 0 ≤ b ∧ b < a ∧ ∀ i ∈ I, q i = b := by
  classical
  obtain ⟨i, hi⟩ : I.Nonempty := card_pos.mp (by omega)
  by_cases hpositive : ∃ j ∈ I, 0 < q j
  · obtain ⟨j, hj, hqj⟩ := hpositive
    have hequal := lower_positive_values_equal_of_no_smaller_repeat hq I C hpart hCI hr
      hw ha hc k hpC hqC hpI hqI hpgrad hqgrad hsmall
    have hvalues : ∀ l ∈ I, q l = 0 ∨ q l = q j := by
      intro l hl
      by_cases hz : q l = 0
      · exact Or.inl hz
      · exact Or.inr (hequal l hl j hj (lt_of_le_of_ne (hq l).1 (Ne.symm hz)) hqj)
    have hnozero : ∀ l ∈ I, q l ≠ 0 := by
      intro l hl hlzero
      let H := I.filter (fun x ↦ q x = q j)
      let Z := I.filter (fun x ↦ q x = 0)
      have hI : I = H ∪ Z := by
        ext x
        simp only [H, Z, mem_filter, mem_union]
        constructor
        · intro hx
          rcases hvalues x hx with hz | hv
          · exact Or.inr ⟨hx, hz⟩
          · exact Or.inl ⟨hx, hv⟩
        · rintro (h | h) <;> exact h.1
      have hHsub : H ⊆ I := filter_subset _ _
      have hZsub : Z ⊆ I := filter_subset _ _
      have hHZ : Disjoint H Z := by
        apply disjoint_left.mpr
        intro x hxH hxZ
        exact hqj.ne' ((mem_filter.mp hxH).2.symm.trans (mem_filter.mp hxZ).2)
      have hcard : I.card = H.card + Z.card := by rw [hI, card_union_of_disjoint hHZ]
      exact not_positive_zero_coordinate_pattern p q C H Z k
        (by rw [hpart, hI, union_assoc]) (hCI.mono_right hHsub) (hCI.mono_right hZsub) hHZ
        ⟨j, by simp [H, hj]⟩ ⟨l, by simp [Z, hl, hlzero]⟩ (by omega)
        hw hqj (hqI j hj) ha hc hpC hqC
        (fun x hx ↦ hpI x (by rw [hI]; exact hx))
        (fun x hx ↦ (mem_filter.mp hx).2) (fun x hx ↦ (mem_filter.mp hx).2)
        (fun x hx ↦ hpgrad x (hHsub hx))
        (fun x hx ↦ hqgrad x (hHsub hx) (by rw [(mem_filter.mp hx).2]; exact hqj))
        (fun x hx ↦ hqzero x (hZsub hx) (mem_filter.mp hx).2)
    refine ⟨q j, hqj.le, hqI j hj, ?_⟩
    intro l hl
    exact (hvalues l hl).resolve_left (hnozero l hl)
  · refine ⟨0, le_rfl, ?_, ?_⟩
    · have hqi : q i = 0 := le_antisymm (le_of_not_gt (fun hp ↦ hpositive ⟨i, hi, hp⟩)) (hq i).1
      simpa only [hqi] using hqI i hi
    · intro l hl
      exact le_antisymm (le_of_not_gt (fun hp ↦ hpositive ⟨l, hl, hp⟩)) (hq l).1

end

end PoissonBinomialComparison
