import PoissonBinomialComparison.SwitchGeometry
import PoissonBinomialComparison.Reflection
import PoissonBinomialComparison.Endpoints

/-!
# Canonical switch functions and the benchmark

Interior switches are selected from their proved unique existence. At gap zero
the parameters equal `j/n`; at gap one they are `(1, 0)`. Outside `[0, 1]` the
definition is extended by these endpoint values. Statements about switches
always retain the manuscript's interior count and gap assumptions.

`switchValue` is `F_{n,j}`, `switchMass` is `f_j`, and `benchmark` is `B_n`.
Endpoint values of the benchmark are set explicitly as in the manuscript.
-/

namespace PoissonBinomialComparison

noncomputable section

/-- The canonical homogeneous switch `(a, b)`, extended by its endpoint values. -/
def switchPair (n j : ℕ) (γ : ℝ) : ℝ × ℝ :=
  if h : 0 < j ∧ j < n ∧ 0 < γ ∧ γ < 1 then
    Classical.choose (existsUnique_switch h.1 h.2.1 h.2.2.1 h.2.2.2).exists
  else if γ ≤ 0 then ((j : ℝ) / n, (j : ℝ) / n) else (1, 0)

/-- Upper parameter `a` of the canonical switch. -/
def switchUpper (n j : ℕ) (γ : ℝ) : ℝ := (switchPair n j γ).1

/-- Lower parameter `b` of the canonical switch. -/
def switchLower (n j : ℕ) (γ : ℝ) : ℝ := (switchPair n j γ).2

/-- The manuscript's homogeneous switching value `F_{n,j}(γ)`. -/
def switchValue (n j : ℕ) (γ : ℝ) : ℝ :=
  tailDiff (fun _ : Fin n ↦ switchUpper n j γ) (fun _ : Fin n ↦ switchLower n j γ) j

/-- The manuscript's common count mass `f_j(γ)` at the switching count. -/
def switchMass (n j : ℕ) (γ : ℝ) : ℝ :=
  pbMass (fun _ : Fin n ↦ switchUpper n j γ) j

/-- The central-switch benchmark `B_n(Δ)`, with the prescribed endpoint values. -/
def benchmark (n : ℕ) (Δ : ℝ) : ℝ :=
  if Δ = 0 then 0 else if Δ = n then 1 else switchValue n (n / 2) (Δ / n)

/-- The selected interior parameters satisfy the exact switch equation and bounds. -/
theorem switchPair_spec {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsSwitch n j γ (switchUpper n j γ) (switchLower n j γ) := by
  have hh : 0 < j ∧ j < n ∧ 0 < γ ∧ γ < 1 := ⟨hj, hjn, hγ0, hγ1⟩
  simp only [switchUpper, switchLower, switchPair, dite_eq_left hh]
  exact Classical.choose_spec (existsUnique_switch hj hjn hγ0 hγ1).exists

/-- Any pair satisfying the switch equation is the canonical pair. -/
theorem IsSwitch.eq_switchPair {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b)
    (hj : 0 < j) (hjn : j < n) :
    a = switchUpper n j γ ∧ b = switchLower n j γ := by
  have hγ0 : 0 < γ := by linarith [h.2.1, h.2.2.2.1]
  have hγ1 : γ < 1 := by linarith [h.1, h.2.2.1, h.2.2.2.1]
  exact switch_unique hj hjn hγ0 h (switchPair_spec hj hjn hγ0 hγ1)

/-- The canonical pair has its prescribed coordinate gap. -/
theorem switchUpper_sub_switchLower {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchUpper n j γ - switchLower n j γ = γ :=
  (switchPair_spec hj hjn hγ0 hγ1).2.2.2.1

/-- The canonical interior switch is an admissible ordered Bernoulli pair. -/
theorem switchPair_admissible {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    AdmissiblePair (fun _ : Fin n ↦ switchUpper n j γ)
      (fun _ : Fin n ↦ switchLower n j γ) := by
  have h := switchPair_spec hj hjn hγ0 hγ1
  rw [admissiblePair_iff]
  intro i
  exact ⟨h.1.le, h.2.1.le, h.2.2.1.le⟩

/-- A switch of coordinate gap `γ` has total gap `nγ`. -/
theorem meanGap_switchPair {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    meanGap (fun _ : Fin n ↦ switchUpper n j γ)
      (fun _ : Fin n ↦ switchLower n j γ) = n * γ := by
  rw [meanGap_const, switchUpper_sub_switchLower hj hjn hγ0 hγ1]

@[simp] theorem switchPair_zero (n j : ℕ) :
    switchPair n j 0 = ((j : ℝ) / n, (j : ℝ) / n) := by
  simp [switchPair]

@[simp] theorem switchPair_one (n j : ℕ) : switchPair n j 1 = (1, 0) := by
  simp [switchPair]

@[simp] theorem switchUpper_zero (n j : ℕ) : switchUpper n j 0 = (j : ℝ) / n := by
  simp [switchUpper]

@[simp] theorem switchLower_zero (n j : ℕ) : switchLower n j 0 = (j : ℝ) / n := by
  simp [switchLower]

@[simp] theorem switchUpper_one (n j : ℕ) : switchUpper n j 1 = 1 := by
  simp [switchUpper]

@[simp] theorem switchLower_one (n j : ℕ) : switchLower n j 1 = 0 := by
  simp [switchLower]

@[simp] theorem switchValue_zero (n j : ℕ) : switchValue n j 0 = 0 := by
  simp [switchValue, tailDiff]

@[simp] theorem switchValue_one {n j : ℕ} (hj : 0 < j) (hjn : j ≤ n) :
    switchValue n j 1 = 1 := by
  simp [switchValue, tailDiff, pbTail_const_one, pbTail_const_zero, hjn, hj.ne']

@[simp] theorem switchMass_zero (n j : ℕ) :
    switchMass n j 0 = (n.choose j : ℝ) * ((j : ℝ) / n) ^ j *
      (1 - (j : ℝ) / n) ^ (n - j) := by
  simp [switchMass, pbMass_const]

@[simp] theorem switchMass_one {n j : ℕ} (hjn : j < n) : switchMass n j 1 = 0 := by
  simp [switchMass, pbMass_const, zero_pow (by omega : n - j ≠ 0)]

/-- The common mass can equivalently be computed from the lower parameters. -/
theorem switchMass_eq_lower {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchMass n j γ = pbMass (fun _ : Fin n ↦ switchLower n j γ) j :=
  (switchPair_spec hj hjn hγ0 hγ1).pbMass_eq

/-- The canonical switching value is also the adjacent threshold difference. -/
theorem switchValue_eq_succ {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchValue n j γ = tailDiff (fun _ : Fin n ↦ switchUpper n j γ)
      (fun _ : Fin n ↦ switchLower n j γ) (j + 1) :=
  (switchPair_spec hj hjn hγ0 hγ1).tailDiff_eq

/-- Canonical switches at reflected counts are complementary pairs. -/
theorem switchPair_reflection {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchUpper n (n - j) γ = 1 - switchLower n j γ ∧
      switchLower n (n - j) γ = 1 - switchUpper n j γ := by
  have h := ((switchPair_spec hj hjn hγ0 hγ1).reflect hjn.le).eq_switchPair
    (by omega : 0 < n - j) (by omega : n - j < n)
  exact ⟨h.1.symm, h.2.symm⟩

/-- The reflected switching values agree, as asserted in the manuscript. -/
theorem switchValue_reflection {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchValue n (n - j) γ = switchValue n j γ := by
  obtain ⟨ha, hb⟩ := switchPair_reflection hj hjn hγ0 hγ1
  unfold switchValue
  rw [ha, hb, tailDiff_reflection _ _ _ (by omega : n - j ≤ n + 1)]
  have hi : n + 1 - (n - j) = j + 1 := by omega
  rw [hi]
  exact (switchValue_eq_succ hj hjn hγ0 hγ1).symm

/-- The common switching masses also agree at reflected counts. -/
theorem switchMass_reflection {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchMass n (n - j) γ = switchMass n j γ := by
  have ha := (switchPair_reflection hj hjn hγ0 hγ1).1
  unfold switchMass
  rw [ha, pbMass_complement _ _ (by omega : n - j ≤ n), Nat.sub_sub_self hjn.le]
  exact (switchMass_eq_lower hj hjn hγ0 hγ1).symm

/-- In even dimension the central switch is exactly the complementary pair. -/
theorem switchPair_even {m : ℕ} (hm : 0 < m)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchUpper (2 * m) m γ = (1 + γ) / 2 ∧
      switchLower (2 * m) m γ = (1 - γ) / 2 := by
  have hn : m < 2 * m := by omega
  have hh := switchPair_reflection hm hn hγ0 hγ1
  have hid : 2 * m - m = m := by omega
  rw [hid] at hh
  have hg := switchUpper_sub_switchLower hm hn hγ0 hγ1
  constructor <;> linarith [hh.1]

private theorem switchPair_of_nonpos (n j : ℕ) {γ : ℝ} (hγ : γ ≤ 0) :
    switchPair n j γ = ((j : ℝ) / n, (j : ℝ) / n) := by
  simp [switchPair, not_lt.mpr hγ, hγ]

private theorem switchPair_of_one_le (n j : ℕ) {γ : ℝ} (hγ : 1 ≤ γ) :
    switchPair n j γ = (1, 0) := by
  have hγ0 : ¬γ ≤ 0 := by linarith
  simp [switchPair, not_lt.mpr hγ, hγ0]

/-- The upper switch parameter has its prescribed continuous extension at zero. -/
theorem continuousAt_switchUpper_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchUpper n j) 0 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro γ hγ
  have hdist : |γ| < min ε 1 := by simpa [Real.dist_eq] using hγ
  have hγ1 : γ < 1 := lt_of_le_of_lt (le_abs_self γ) (lt_min_iff.mp hdist).2
  by_cases hγ0 : γ ≤ 0
  · simp [switchUpper, switchPair_of_nonpos n j hγ0, hε]
  · have hs := switchPair_spec hj hjn (lt_of_not_ge hγ0) hγ1
    have hc := hs.center_bounds hj hjn
    rw [switchUpper_zero, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hc.2.le)]
    have hg := hs.2.2.2.1
    have hγε : γ < ε := lt_of_le_of_lt (le_abs_self γ) (lt_min_iff.mp hdist).1
    linarith [hc.1]

/-- The lower switch parameter has its prescribed continuous extension at zero. -/
theorem continuousAt_switchLower_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchLower n j) 0 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro γ hγ
  have hdist : |γ| < min ε 1 := by simpa [Real.dist_eq] using hγ
  have hγ1 : γ < 1 := lt_of_le_of_lt (le_abs_self γ) (lt_min_iff.mp hdist).2
  by_cases hγ0 : γ ≤ 0
  · simp [switchLower, switchPair_of_nonpos n j hγ0, hε]
  · have hs := switchPair_spec hj hjn (lt_of_not_ge hγ0) hγ1
    have hc := hs.center_bounds hj hjn
    rw [switchLower_zero, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hc.1.le)]
    have hg := hs.2.2.2.1
    have hγε : γ < ε := lt_of_le_of_lt (le_abs_self γ) (lt_min_iff.mp hdist).1
    linarith [hc.2]

/-- The upper switch parameter tends continuously to one at gap one. -/
theorem continuousAt_switchUpper_one {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchUpper n j) 1 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro γ hγ
  have hdist : |γ - 1| < min ε 1 := by simpa [Real.dist_eq] using hγ
  have hγ0 : 0 < γ := by have := (abs_lt.mp ((lt_min_iff.mp hdist).2)).1; linarith
  by_cases hγ1 : 1 ≤ γ
  · simp [switchUpper, switchPair_of_one_le n j hγ1, hε]
  · have hs := switchPair_spec hj hjn hγ0 (lt_of_not_ge hγ1)
    rw [switchUpper_one, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2.2.1.le)]
    have hg := hs.2.2.2.1
    have hγε := (abs_lt.mp ((lt_min_iff.mp hdist).1)).1
    linarith [hs.1]

/-- The lower switch parameter tends continuously to zero at gap one. -/
theorem continuousAt_switchLower_one {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchLower n j) 1 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro γ hγ
  have hdist : |γ - 1| < min ε 1 := by simpa [Real.dist_eq] using hγ
  have hγ0 : 0 < γ := by have := (abs_lt.mp ((lt_min_iff.mp hdist).2)).1; linarith
  by_cases hγ1 : 1 ≤ γ
  · simp [switchLower, switchPair_of_one_le n j hγ1, hε]
  · have hs := switchPair_spec hj hjn hγ0 (lt_of_not_ge hγ1)
    rw [switchLower_one, Real.dist_eq, sub_zero, abs_of_nonneg hs.1.le]
    have hg := hs.2.2.2.1
    have hγε := (abs_lt.mp ((lt_min_iff.mp hdist).1)).1
    linarith [hs.2.2.1]

/-- Continuity of the parameters implies continuity of the switching value. -/
theorem continuousAt_switchValue_of_parameters (n j : ℕ) (γ : ℝ)
    (ha : ContinuousAt (switchUpper n j) γ) (hb : ContinuousAt (switchLower n j) γ) :
    ContinuousAt (switchValue n j) γ := by
  change ContinuousAt (fun u ↦ tailDiff (fun _ : Fin n ↦ switchUpper n j u)
    (fun _ : Fin n ↦ switchLower n j u) j) γ
  simp only [tailDiff, pbTail_const]
  fun_prop

/-- Continuity of the upper parameter implies continuity of the common mass. -/
theorem continuousAt_switchMass_of_upper (n j : ℕ) (γ : ℝ)
    (ha : ContinuousAt (switchUpper n j) γ) : ContinuousAt (switchMass n j) γ := by
  change ContinuousAt (fun u ↦ pbMass (fun _ : Fin n ↦ switchUpper n j u) j) γ
  simp only [pbMass_const]
  fun_prop

/-- The switching value extends continuously to gap zero. -/
theorem continuousAt_switchValue_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchValue n j) 0 :=
  continuousAt_switchValue_of_parameters n j 0
    (continuousAt_switchUpper_zero hj hjn) (continuousAt_switchLower_zero hj hjn)

/-- The switching value extends continuously to gap one. -/
theorem continuousAt_switchValue_one {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchValue n j) 1 :=
  continuousAt_switchValue_of_parameters n j 1
    (continuousAt_switchUpper_one hj hjn) (continuousAt_switchLower_one hj hjn)

/-- The switching mass extends continuously to gap zero. -/
theorem continuousAt_switchMass_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchMass n j) 0 :=
  continuousAt_switchMass_of_upper n j 0 (continuousAt_switchUpper_zero hj hjn)

/-- The switching mass extends continuously to gap one. -/
theorem continuousAt_switchMass_one {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchMass n j) 1 :=
  continuousAt_switchMass_of_upper n j 1 (continuousAt_switchUpper_one hj hjn)

@[simp] theorem benchmark_zero (n : ℕ) : benchmark n 0 = 0 := by simp [benchmark]

@[simp] theorem benchmark_at_dimension {n : ℕ} (hn : 0 < n) : benchmark n n = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [benchmark, hn']

/-- Away from its endpoints the benchmark is exactly the central switching value. -/
theorem benchmark_eq_switchValue {n : ℕ} {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    benchmark n Δ = switchValue n (n / 2) (Δ / n) := by
  simp [benchmark, hΔ0.ne', hΔn.ne]

end

end PoissonBinomialComparison
