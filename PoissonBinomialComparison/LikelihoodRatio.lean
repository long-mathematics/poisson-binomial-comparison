import PoissonBinomialComparison.LogConcavity

/-!
# Likelihood-ratio order for Bernoulli sums

The order is expressed by cross multiplication, so zero endpoint masses require
no division conventions. Integer indexing is the zero extension of the original
finite subset-sum mass function.
-/

namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

/-- Likelihood-ratio order, written without division at zero masses. -/
def LikelihoodRatioLE (f g : ℤ → ℝ) : Prop :=
  ∀ i j : ℤ, i ≤ j → g i * f j ≤ g j * f i

/-- Convolution with one Bernoulli parameter. -/
def bernoulliConvolve (f : ℤ → ℝ) (t : ℝ) (k : ℤ) : ℝ :=
  (1 - t) * f k + t * f (k - 1)

theorem LikelihoodRatioLE.refl (f : ℤ → ℝ) : LikelihoodRatioLE f f := by
  intro i j _
  exact le_of_eq (mul_comm _ _)

/-- Likelihood-ratio order is transitive for nonnegative, nonzero mass functions. -/
theorem LikelihoodRatioLE.trans {f g h : ℤ → ℝ}
    (hfg : LikelihoodRatioLE f g) (hgh : LikelihoodRatioLE g h)
    (hf : ∀ k, 0 ≤ f k) (hh : ∀ k, 0 ≤ h k)
    (hgne : ∃ k, 0 < g k) : LikelihoodRatioLE f h := by
  intro i j hij
  by_cases hpos : 0 < h i * f j
  · have hip := pos_of_mul_pos_left hpos (hf j)
    have fjp := pos_of_mul_pos_right hpos (hh i)
    obtain ⟨k, hkp⟩ := hgne
    have gip : 0 < g i := by
      rcases le_total k i with hki | hik
      · have gjp := pos_of_mul_pos_left
          ((mul_pos hkp fjp).trans_le (hfg k j (hki.trans hij))) (hf k)
        exact pos_of_mul_pos_right ((mul_pos hip gjp).trans_le (hgh i j hij)) (hh j)
      · exact pos_of_mul_pos_right ((mul_pos hip hkp).trans_le (hgh i k hik)) (hh k)
    have gjp := pos_of_mul_pos_left
      ((mul_pos gip fjp).trans_le (hfg i j hij)) (hf i)
    apply (mul_le_mul_iff_right₀ gjp).mp
    have h1 := mul_le_mul_of_nonneg_right (hgh i j hij) (hf j)
    have h2 := mul_le_mul_of_nonneg_left (hfg i j hij) (hh j)
    nlinarith
  · exact (le_of_not_gt hpos).trans (mul_nonneg (hh j) (hf i))

/-- Common Bernoulli convolution preserves likelihood-ratio order. -/
theorem LikelihoodRatioLE.convolve {f g : ℤ → ℝ}
    (h : LikelihoodRatioLE f g) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    LikelihoodRatioLE (bernoulliConvolve f t) (bernoulliConvolve g t) := by
  intro i j hij
  by_cases heq : i = j
  · subst j
    exact le_rfl
  have h1 := mul_le_mul_of_nonneg_left (h i j hij) (sq_nonneg (1 - t))
  have h2 := mul_le_mul_of_nonneg_left (h (i - 1) (j - 1) (by omega)) (sq_nonneg t)
  have h3 := mul_le_mul_of_nonneg_left (h (i - 1) j (by omega))
    (mul_nonneg ht0 (sub_nonneg.mpr ht1))
  have h4 := mul_le_mul_of_nonneg_left (h i (j - 1) (by omega))
    (mul_nonneg ht0 (sub_nonneg.mpr ht1))
  unfold bernoulliConvolve
  nlinarith

/-- Exact determinant for changing a single Bernoulli parameter. -/
theorem bernoulliConvolve_determinant (f : ℤ → ℝ) (a b : ℝ) (i j : ℤ) :
    bernoulliConvolve f b j * bernoulliConvolve f a i -
      bernoulliConvolve f b i * bernoulliConvolve f a j =
        (b - a) * (f i * f (j - 1) - f (i - 1) * f j) := by
  unfold bernoulliConvolve
  ring

/-- Increasing the parameter increases likelihood-ratio order of a Bernoulli convolution. -/
theorem bernoulliConvolve_likelihoodRatio {f : ℤ → ℝ}
    (hf : MassCrossInequalities f) {a b : ℝ} (hab : a ≤ b) :
    LikelihoodRatioLE (bernoulliConvolve f a) (bernoulliConvolve f b) := by
  intro i j hij
  by_cases heq : i = j
  · subst j
    exact le_rfl
  apply sub_nonneg.mp
  rw [bernoulliConvolve_determinant]
  apply mul_nonneg (sub_nonneg.mpr hab)
  apply sub_nonneg.mpr
  simpa using hf i (j - 1) (by omega)

/-- Positive adjacent convolved masses force the intervening deleted mass to be positive. -/
theorem bernoulliConvolve_middle_pos {f : ℤ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hc : MassCrossInequalities f)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℤ)
    (h0 : 0 < bernoulliConvolve f a k)
    (h1 : 0 < bernoulliConvolve f a (k + 1)) : 0 < f k := by
  by_contra hnot
  have hk : f k = 0 := le_antisymm (le_of_not_gt hnot) (hf k)
  have hleft : 0 < a * f (k - 1) := by simpa [bernoulliConvolve, hk] using h0
  have hright : 0 < (1 - a) * f (k + 1) := by
    simpa [bernoulliConvolve, hk] using h1
  have hl := pos_of_mul_pos_right hleft ha0
  have hr := pos_of_mul_pos_right hright (sub_nonneg.mpr ha1)
  have hcross := hc k k le_rfl
  rw [hk, zero_mul] at hcross
  exact (not_lt_of_ge hcross) (mul_pos hl hr)

/-- Strict parameter increase gives a strict adjacent determinant when the old
adjacent masses are positive; this implies the manuscript's four-positive-mass case. -/
theorem bernoulliConvolve_strict_adjacent {f : ℤ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hc : MassCrossInequalities f)
    (hs : StrictMassLogConcavity f) {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hab : a < b) (k : ℤ)
    (h0 : 0 < bernoulliConvolve f a k)
    (h1 : 0 < bernoulliConvolve f a (k + 1)) :
    bernoulliConvolve f b k * bernoulliConvolve f a (k + 1) <
      bernoulliConvolve f b (k + 1) * bernoulliConvolve f a k := by
  apply sub_pos.mp
  rw [bernoulliConvolve_determinant]
  have hstrict := hs k (bernoulliConvolve_middle_pos hf hc ha0 ha1 k h0 h1)
  simp only [add_sub_cancel_right]
  exact mul_pos (sub_pos.mpr hab) (by nlinarith)

theorem bernoulliConvolve_nonneg {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (k : ℤ) :
    0 ≤ bernoulliConvolve f t k :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hf k)) (mul_nonneg ht0 (hf (k - 1)))

theorem bernoulliConvolve_exists_pos {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hne : ∃ k, 0 < f k) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ k, 0 < bernoulliConvolve f t k := by
  obtain ⟨k, hk⟩ := hne
  by_cases ht : t = 1
  · exact ⟨k + 1, by simpa [bernoulliConvolve, ht] using hk⟩
  · refine ⟨k, ?_⟩
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht1 ht)) hk) (mul_nonneg ht0 (hf (k - 1)))

/-- Strict adjacent comparison survives further likelihood-ratio increase when
the final upper mass is positive. -/
theorem LikelihoodRatioLE.strict_adjacent_trans {f g h : ℤ → ℝ}
    (hgh : LikelihoodRatioLE g h) (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k)
    (k : ℤ) (hstrict : g k * f (k + 1) < g (k + 1) * f k)
    (hh : 0 < h (k + 1)) :
    h k * f (k + 1) < h (k + 1) * f k := by
  have hgp : 0 < g (k + 1) := pos_of_mul_pos_left
    ((mul_nonneg (hg k) (hf (k + 1))).trans_lt hstrict) (hf k)
  apply (mul_lt_mul_iff_right₀ hgp).mp
  have h1 := mul_lt_mul_of_pos_left hstrict hh
  have h2 := mul_le_mul_of_nonneg_right (hgh k (k + 1) (by omega)) (hf (k + 1))
  nlinarith

variable {ι : Type*} [DecidableEq ι]

theorem pbMassIntOn_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (k : ℤ) :
    pbMassIntOn p s k = pbMassIntOn q s k := by
  unfold pbMassIntOn
  split
  · exact pbMassOn_congr h _
  · rfl

theorem pbMassIntOn_update_of_notMem (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (a : ℝ) (k : ℤ) :
    pbMassIntOn (Function.update p i a) s k = pbMassIntOn p s k := by
  unfold pbMassIntOn
  split
  · exact pbMassOn_update_of_notMem p hi a _
  · rfl

theorem pbMassIntOn_update_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (a : ℝ) :
    pbMassIntOn (Function.update p i a) (insert i s) =
      bernoulliConvolve (pbMassIntOn p s) a := by
  funext k
  rw [pbMassIntOn_insert _ hi]
  simp only [Function.update_self, pbMassIntOn_update_of_notMem p hi, bernoulliConvolve]

theorem pbMassIntOn_exists_pos {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) : ∃ k : ℤ, 0 < pbMassIntOn p s k := by
  have hsum : 0 < ∑ k ∈ range (s.card + 1), pbMassOn p s k := by
    rw [sum_pbMassOn]
    norm_num
  obtain ⟨k, _, hk⟩ := (sum_pos_iff_of_nonneg (fun k _ ↦ pbMassOn_nonneg hp k)).mp hsum
  exact ⟨k, by simpa using hk⟩

/-- Single-coordinate likelihood-ratio order on arbitrary finite coordinate sets. -/
theorem pbMassIntOn_update_likelihoodRatio (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    LikelihoodRatioLE (pbMassIntOn (Function.update p i a) (insert i s))
      (pbMassIntOn (Function.update p i b) (insert i s)) := by
  rw [pbMassIntOn_update_insert p hi a, pbMassIntOn_update_insert p hi b]
  exact bernoulliConvolve_likelihoodRatio (pbMassIntOn_cross s hp) hab

/-- Arbitrary coordinatewise increases preserve likelihood-ratio order. -/
theorem pbMassIntOn_likelihoodRatio {p q : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, p i ≤ q i) :
    LikelihoodRatioLE (pbMassIntOn p s) (pbMassIntOn q s) := by
  induction s using Finset.induction_on with
  | empty =>
    intro i j hij
    simp only [pbMassIntOn_empty]
    exact le_of_eq (mul_comm _ _)
  | @insert i s hi ih =>
    have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 :=
      fun j hj ↦ hp j (mem_insert_of_mem hj)
    have hqs : ∀ j ∈ s, 0 ≤ q j ∧ q j ≤ 1 :=
      fun j hj ↦ hq j (mem_insert_of_mem hj)
    have hpqs : ∀ j ∈ s, p j ≤ q j := fun j hj ↦ hpq j (mem_insert_of_mem hj)
    have hpi := hp i (mem_insert_self i s)
    have hqi := hq i (mem_insert_self i s)
    have heqp : pbMassIntOn p (insert i s) = bernoulliConvolve (pbMassIntOn p s) (p i) :=
      funext (pbMassIntOn_insert p hi)
    have heqq : pbMassIntOn q (insert i s) = bernoulliConvolve (pbMassIntOn q s) (q i) :=
      funext (pbMassIntOn_insert q hi)
    rw [heqp, heqq]
    exact ((ih hps hqs hpqs).convolve hpi.1 hpi.2).trans
      (bernoulliConvolve_likelihoodRatio (pbMassIntOn_cross s hqs) (hpq i (mem_insert_self i s)))
      (bernoulliConvolve_nonneg (pbMassIntOn_nonneg hps) hpi.1 hpi.2)
      (bernoulliConvolve_nonneg (pbMassIntOn_nonneg hqs) hqi.1 hqi.2)
      (bernoulliConvolve_exists_pos (pbMassIntOn_nonneg hqs) (pbMassIntOn_exists_pos s hqs)
        hpi.1 hpi.2)

/-- Strict adjacent likelihood-ratio comparison for one coordinate update. -/
theorem pbMassIntOn_update_strict_adjacent (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1)
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hab : a < b) (k : ℤ)
    (h0 : 0 < pbMassIntOn (Function.update p i a) (insert i s) k)
    (h1 : 0 < pbMassIntOn (Function.update p i a) (insert i s) (k + 1)) :
    pbMassIntOn (Function.update p i b) (insert i s) k *
        pbMassIntOn (Function.update p i a) (insert i s) (k + 1) <
      pbMassIntOn (Function.update p i b) (insert i s) (k + 1) *
        pbMassIntOn (Function.update p i a) (insert i s) k := by
  rw [pbMassIntOn_update_insert p hi a] at h0 h1
  rw [pbMassIntOn_update_insert p hi a, pbMassIntOn_update_insert p hi b]
  exact bernoulliConvolve_strict_adjacent (pbMassIntOn_nonneg hp) (pbMassIntOn_cross s hp)
    (pbMassIntOn_strictLogConcavity s hp) ha0 ha1 hab k h0 h1

/-- Any strict coordinate increase gives strict adjacent comparison when the old
adjacent masses and the new upper mass are positive. -/
theorem pbMassIntOn_strict_adjacent {p q : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, p i ≤ q i) (hstrict : ∃ i ∈ s, p i < q i) (k : ℤ)
    (hp0 : 0 < pbMassIntOn p s k) (hp1 : 0 < pbMassIntOn p s (k + 1))
    (hq1 : 0 < pbMassIntOn q s (k + 1)) :
    pbMassIntOn q s k * pbMassIntOn p s (k + 1) <
      pbMassIntOn q s (k + 1) * pbMassIntOn p s k := by
  obtain ⟨i, hi, hpi⟩ := hstrict
  let r := Function.update p i (q i)
  have hr : ∀ j ∈ s, 0 ≤ r j ∧ r j ≤ 1 := by
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa [r] using hq i hi
    · simpa [r, Function.update_of_ne hji] using hp j hj
  have hrq : ∀ j ∈ s, r j ≤ q j := by
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [r]
    · simpa [r, Function.update_of_ne hji] using hpq j hj
  have hpr : pbMassIntOn r s k * pbMassIntOn p s (k + 1) <
      pbMassIntOn r s (k + 1) * pbMassIntOn p s k := by
    have hd := pbMassIntOn_update_strict_adjacent p (notMem_erase i s)
      (fun j hj ↦ hp j (mem_erase.mp hj).2) (hp i hi).1 (hp i hi).2 hpi k
    simpa [Function.update_eq_self, insert_erase hi, r] using hd
      (by simpa [Function.update_eq_self, insert_erase hi] using hp0)
      (by simpa [Function.update_eq_self, insert_erase hi] using hp1)
  exact (pbMassIntOn_likelihoodRatio s hr hq hrq).strict_adjacent_trans
    (pbMassIntOn_nonneg hp) (pbMassIntOn_nonneg hr) k hpr hq1

/-- Adjoining a Bernoulli variable increases likelihood-ratio order. -/
theorem pbMassIntOn_adjoin_likelihoodRatio (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1) (hpi : 0 ≤ p i) :
    LikelihoodRatioLE (pbMassIntOn p s) (pbMassIntOn p (insert i s)) := by
  have h := bernoulliConvolve_likelihoodRatio (pbMassIntOn_cross s hp) hpi
  have hzero : bernoulliConvolve (pbMassIntOn p s) 0 = pbMassIntOn p s := by
    funext k
    simp [bernoulliConvolve]
  have heq : pbMassIntOn p (insert i s) = bernoulliConvolve (pbMassIntOn p s) (p i) :=
    funext (pbMassIntOn_insert p hi)
  rwa [hzero, ← heq] at h

/-- Adjoining a positive Bernoulli parameter gives strict adjacent comparison
where the original adjacent masses are positive. -/
theorem pbMassIntOn_adjoin_strict_adjacent (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1) (hpi : 0 < p i) (k : ℤ)
    (h0 : 0 < pbMassIntOn p s k) (h1 : 0 < pbMassIntOn p s (k + 1)) :
    pbMassIntOn p (insert i s) k * pbMassIntOn p s (k + 1) <
      pbMassIntOn p (insert i s) (k + 1) * pbMassIntOn p s k := by
  have hzero : bernoulliConvolve (pbMassIntOn p s) 0 = pbMassIntOn p s := by
    funext j
    simp [bernoulliConvolve]
  have heq : pbMassIntOn p (insert i s) = bernoulliConvolve (pbMassIntOn p s) (p i) :=
    funext (pbMassIntOn_insert p hi)
  have h := bernoulliConvolve_strict_adjacent (pbMassIntOn_nonneg hp)
    (pbMassIntOn_cross s hp) (pbMassIntOn_strictLogConcavity s hp)
    (a := 0) (by norm_num) (by norm_num) hpi k (by rwa [hzero]) (by rwa [hzero])
  simpa only [hzero, ← heq] using h

/-- Equal positive adjacent masses become strictly increasing after a strict
parameter increase, provided the new upper mass remains positive. -/
theorem pbMassIntOn_equal_adjacent_increase {p q : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, p i ≤ q i) (hstrict : ∃ i ∈ s, p i < q i) (k : ℤ)
    (heq : pbMassIntOn p s k = pbMassIntOn p s (k + 1))
    (hp1 : 0 < pbMassIntOn p s (k + 1)) (hq1 : 0 < pbMassIntOn q s (k + 1)) :
    pbMassIntOn q s k < pbMassIntOn q s (k + 1) := by
  have h := pbMassIntOn_strict_adjacent s hp hq hpq hstrict k (by rwa [heq]) hp1 hq1
  rw [heq] at h
  exact (mul_lt_mul_iff_left₀ hp1).mp h

/-- If an upper mass disappears under parameter increase, the adjacent lower
mass also vanishes whenever the old upper mass was positive. -/
theorem pbMassIntOn_adjacent_disappear {p q : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, p i ≤ q i) (k : ℤ)
    (hp1 : 0 < pbMassIntOn p s (k + 1)) (hq1 : pbMassIntOn q s (k + 1) = 0) :
    pbMassIntOn q s k = 0 := by
  have h := pbMassIntOn_likelihoodRatio s hp hq hpq k (k + 1) (by omega)
  rw [hq1, zero_mul] at h
  apply le_antisymm _ (pbMassIntOn_nonneg hq k)
  by_contra hnot
  exact (not_lt_of_ge h) (mul_pos (lt_of_not_ge hnot) hp1)

/-- Once the lower-minus-upper adjacent difference is nonpositive, a strict
parameter increase makes it negative on positive overlapping support. -/
theorem pbMassIntOn_adjacent_sign_preserved {p q : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, p i ≤ q i) (hstrict : ∃ i ∈ s, p i < q i) (k : ℤ)
    (hp0 : 0 < pbMassIntOn p s k) (hp1 : 0 < pbMassIntOn p s (k + 1))
    (horder : pbMassIntOn p s k ≤ pbMassIntOn p s (k + 1))
    (hq1 : 0 < pbMassIntOn q s (k + 1)) :
    pbMassIntOn q s k < pbMassIntOn q s (k + 1) := by
  have h := pbMassIntOn_strict_adjacent s hp hq hpq hstrict k hp0 hp1 hq1
  exact (mul_lt_mul_iff_left₀ hp1).mp
    (h.trans_le (mul_le_mul_of_nonneg_left horder hq1.le))

variable {n : ℕ}

/-- Manuscript likelihood-ratio comparison for ordered parameter vectors. -/
theorem pbMass_likelihoodRatio {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (i j : ℕ) (hij : i ≤ j) :
    pbMass p i * pbMass q j ≤ pbMass p j * pbMass q i := by
  have h' := pbMassIntOn_likelihoodRatio univ (fun i _ ↦ h.2.1 i)
    (fun i _ ↦ h.1 i) (fun i _ ↦ h.2.2 i) (i : ℤ) (j : ℤ) (by omega)
  simpa [pbMass] using h'

/-- Manuscript strict adjacent comparison. Positivity of the new lower mass
is unnecessary, so this includes the four-positive-mass statement. -/
theorem pbMass_strict_adjacent_likelihoodRatio {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hstrict : ∃ i, q i < p i) (k : ℕ)
    (hq0 : 0 < pbMass q k) (hq1 : 0 < pbMass q (k + 1))
    (hp1 : 0 < pbMass p (k + 1)) :
    pbMass p k * pbMass q (k + 1) < pbMass p (k + 1) * pbMass q k := by
  have hs : ∃ i ∈ (univ : Finset (Fin n)), q i < p i := by simpa using hstrict
  have hc : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
  have h' := pbMassIntOn_strict_adjacent univ (fun i _ ↦ h.2.1 i)
    (fun i _ ↦ h.1 i) (fun i _ ↦ h.2.2 i) hs (k : ℤ)
    (by simpa only [pbMassIntOn_natCast, pbMass] using hq0)
    (by simpa only [hc, pbMassIntOn_natCast, pbMass] using hq1)
    (by simpa only [hc, pbMassIntOn_natCast, pbMass] using hp1)
  simpa only [hc, pbMassIntOn_natCast, pbMass] using h'

/-- Manuscript equal-adjacent-mass consequence of strict parameter increase. -/
theorem pbMass_equal_adjacent_increase {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hstrict : ∃ i, q i < p i) (k : ℕ)
    (heq : pbMass q k = pbMass q (k + 1))
    (hq1 : 0 < pbMass q (k + 1)) (hp1 : 0 < pbMass p (k + 1)) :
    pbMass p k < pbMass p (k + 1) := by
  have h' := pbMass_strict_adjacent_likelihoodRatio h hstrict k (by rwa [heq]) hq1 hp1
  rw [heq] at h'
  exact (mul_lt_mul_iff_left₀ hq1).mp h'

/-- Manuscript zero-mass endpoint consequence, requiring only old upper positivity. -/
theorem pbMass_adjacent_disappear {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (k : ℕ) (hq1 : 0 < pbMass q (k + 1)) (hp1 : pbMass p (k + 1) = 0) :
    pbMass p k = 0 := by
  have h' := pbMass_likelihoodRatio h k (k + 1) (by omega)
  rw [hp1, zero_mul] at h'
  apply le_antisymm _ (pbMass_nonneg h.1 k)
  by_contra hnot
  exact (not_lt_of_ge h') (mul_pos (lt_of_not_ge hnot) hq1)

/-- Adjacent differences can cross zero only from positive to negative under
strict parameter increases while the required masses stay positive. -/
theorem pbMass_adjacent_sign_preserved {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hstrict : ∃ i, q i < p i) (k : ℕ)
    (hq0 : 0 < pbMass q k) (hq1 : 0 < pbMass q (k + 1))
    (horder : pbMass q k ≤ pbMass q (k + 1)) (hp1 : 0 < pbMass p (k + 1)) :
    pbMass p k < pbMass p (k + 1) := by
  have h' := pbMass_strict_adjacent_likelihoodRatio h hstrict k hq0 hq1 hp1
  exact (mul_lt_mul_iff_left₀ hq1).mp
    (h'.trans_le (mul_le_mul_of_nonneg_left horder hp1.le))

end

end PoissonBinomialComparison
