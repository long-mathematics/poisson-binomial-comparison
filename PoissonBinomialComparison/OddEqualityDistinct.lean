import PoissonBinomialComparison.HomogeneousEquality

/-! # The two odd-dimensional equality pairs are distinct

The odd central switch cannot be complementary: its equal-height equation
would then force the two strictly ordered parameters to coincide.
-/

namespace PoissonBinomialComparison

/-- An odd central switch is never complementary. -/
theorem IsSwitch.odd_not_complementary {m : ℕ} {γ a b : ℝ}
    (h : IsSwitch (2*m+1) m γ a b) : a+b ≠ 1 := by
  intro hab
  have ha : 0 < a := h.1.trans h.2.1
  have h1a : 1-a = b := by linarith
  have h1b : 1-b = a := by linarith
  have heq := h.2.2.2.2
  rw [show 2*m+1-m = m+1 by omega,h1a,h1b,pow_succ,pow_succ] at heq
  have hf : a^m*b^m ≠ 0 := mul_ne_zero (pow_ne_zero _ ha.ne') (pow_ne_zero _ h.1.ne')
  have he : (a^m*b^m)*b = (a^m*b^m)*a := by nlinarith only [heq]
  exact h.2.1.ne (mul_left_cancel₀ hf he)

/-- The homogeneous odd central switch and its reflected pair are different. -/
theorem IsSwitch.odd_pair_ne_reflection {m : ℕ} {γ a b : ℝ}
    (h : IsSwitch (2*m+1) m γ a b) :
    ((fun _ : Fin (2*m+1) => a),(fun _ : Fin (2*m+1) => b)) ≠
      ((fun _ : Fin (2*m+1) => 1-b),(fun _ : Fin (2*m+1) => 1-a)) := by
  intro heq
  have ha := congrFun (congrArg Prod.fst heq) ⟨0,by omega⟩
  apply h.odd_not_complementary
  dsimp at ha
  linarith

/-- The two canonical odd-dimensional equality pairs are genuinely distinct. -/
theorem odd_switchPair_ne_reflection {m : ℕ} (hm : 0 < m) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ((fun _ : Fin (2*m+1) => switchUpper (2*m+1) m γ),
      (fun _ : Fin (2*m+1) => switchLower (2*m+1) m γ)) ≠
    ((fun _ : Fin (2*m+1) => 1-switchLower (2*m+1) m γ),
      (fun _ : Fin (2*m+1) => 1-switchUpper (2*m+1) m γ)) :=
  (switchPair_spec hm (by omega) hγ0 hγ1).odd_pair_ne_reflection

end PoissonBinomialComparison
