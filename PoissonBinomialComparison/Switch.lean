import PoissonBinomialComparison.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Existence and uniqueness of homogeneous switches

The switch equation is precisely the manuscript's equal-height equation.
Existence uses the intermediate value theorem for a polynomial; uniqueness
uses two strictly decreasing positive ratios, without differential calculus.
Only interior gaps are considered here; no endpoint extension is defined.
-/

namespace PoissonBinomialComparison

/-- A homogeneous switch at count `j` with coordinate gap `γ`. -/
def IsSwitch (n j : ℕ) (γ a b : ℝ) : Prop :=
  0 < b ∧ b < a ∧ a < 1 ∧ a - b = γ ∧
    a ^ j * (1 - a) ^ (n - j) = b ^ j * (1 - b) ^ (n - j)

private theorem switch_ratio_strictAntiOn {n j : ℕ} {γ : ℝ}
    (hj : 0 < j) (hjn : j < n) (hγ : 0 < γ) :
    StrictAntiOn
      (fun b : ℝ ↦ ((b + γ) / b) ^ j * ((1 - (b + γ)) / (1 - b)) ^ (n - j))
      (Set.Ioo 0 (1 - γ)) := by
  intro b₁ hb₁ b₂ hb₂ hlt
  have hb₁' : 0 < 1 - b₁ := by linarith [hb₁.2]
  have hb₂' : 0 < 1 - b₂ := by linarith [hb₂.2]
  have hr₁ : (b₂ + γ) / b₂ < (b₁ + γ) / b₁ := by
    apply (div_lt_div_iff₀ hb₂.1 hb₁.1).2
    nlinarith
  have hr₂ : (1 - (b₂ + γ)) / (1 - b₂) <
      (1 - (b₁ + γ)) / (1 - b₁) := by
    apply (div_lt_div_iff₀ hb₂' hb₁').2
    nlinarith
  have hp₁ : 0 < (b₂ + γ) / b₂ := div_pos (by linarith [hb₂.1]) hb₂.1
  have hp₂ : 0 < (1 - (b₁ + γ)) / (1 - b₁) :=
    div_pos (by linarith [hb₁.2]) hb₁'
  have hp₂' : 0 < (1 - (b₂ + γ)) / (1 - b₂) :=
    div_pos (by linarith [hb₂.2]) hb₂'
  exact mul_lt_mul_of_pos
    (pow_lt_pow_left₀ hr₁ hp₁.le (by omega))
    (pow_lt_pow_left₀ hr₂ hp₂'.le (by omega))
    (pow_pos hp₁ _) (pow_pos hp₂ _)

private theorem switch_ratio_eq_one {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) :
    ((b + γ) / b) ^ j * ((1 - (b + γ)) / (1 - b)) ^ (n - j) = 1 := by
  have ha : b + γ = a := by linarith [h.2.2.2.1]
  have hb : 0 < 1 - b := by linarith [h.2.1, h.2.2.1]
  rw [ha, div_pow, div_pow, div_mul_div_comm, h.2.2.2.2]
  exact div_self (ne_of_gt (mul_pos (pow_pos h.1 _) (pow_pos hb _)))

/-- A switch exists for every interior gap and every nonendpoint count. -/
theorem exists_switch {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ a b : ℝ, IsSwitch n j γ a b := by
  let H : ℝ → ℝ := fun b ↦
    (b + γ) ^ j * (1 - (b + γ)) ^ (n - j) - b ^ j * (1 - b) ^ (n - j)
  have hj0 : j ≠ 0 := by omega
  have hnj0 : n - j ≠ 0 := by omega
  have H0 : 0 < H 0 := by
    simp only [H, zero_add, zero_pow hj0, zero_mul, sub_zero]
    exact mul_pos (pow_pos hγ0 _) (pow_pos (by linarith) _)
  have H1 : H (1 - γ) < 0 := by
    have heq : 1 - γ + γ = 1 := by ring
    simp only [H, heq, sub_self, zero_pow hnj0, mul_zero, zero_sub]
    exact neg_neg_of_pos (mul_pos (pow_pos (by linarith) _) (pow_pos (by linarith) _))
  have hcont : ContinuousOn H (Set.Icc 0 (1 - γ)) := by
    dsimp [H]
    fun_prop
  obtain ⟨b, hb, heq⟩ :=
    intermediate_value_Icc' (by linarith : 0 ≤ 1 - γ) hcont ⟨H1.le, H0.le⟩
  have hb0 : 0 < b := by
    apply lt_of_le_of_ne hb.1
    intro he
    subst b
    linarith
  have hb1 : b < 1 - γ := by
    apply lt_of_le_of_ne hb.2
    intro he
    rw [he] at heq
    linarith
  refine ⟨b + γ, b, hb0, by linarith, by linarith, by ring, ?_⟩
  exact sub_eq_zero.mp heq

/-- Both parameters of an interior switch are uniquely determined. -/
theorem switch_unique {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ a₁ b₁ a₂ b₂ : ℝ} (hγ : 0 < γ)
    (h₁ : IsSwitch n j γ a₁ b₁) (h₂ : IsSwitch n j γ a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hb₁ : b₁ ∈ Set.Ioo 0 (1 - γ) :=
    ⟨h₁.1, by linarith [h₁.2.2.1, h₁.2.2.2.1]⟩
  have hb₂ : b₂ ∈ Set.Ioo 0 (1 - γ) :=
    ⟨h₂.1, by linarith [h₂.2.2.1, h₂.2.2.2.1]⟩
  have heq : b₁ = b₂ := (switch_ratio_strictAntiOn hj hjn hγ).injOn hb₁ hb₂
    ((switch_ratio_eq_one h₁).trans (switch_ratio_eq_one h₂).symm)
  exact ⟨by linarith [h₁.2.2.2.1, h₂.2.2.2.1], heq⟩

/-- The unique homogeneous switch, expressed as an ordered pair `(a, b)`. -/
theorem existsUnique_switch {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃! ab : ℝ × ℝ, IsSwitch n j γ ab.1 ab.2 := by
  obtain ⟨a, b, h⟩ := exists_switch hj hjn hγ0 hγ1
  refine ⟨(a, b), h, ?_⟩
  intro ab hab
  exact Prod.ext (switch_unique hj hjn hγ0 hab h).1 (switch_unique hj hjn hγ0 hab h).2

end PoissonBinomialComparison
