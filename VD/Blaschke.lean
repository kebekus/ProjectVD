import Mathlib.Analysis.Meromorphic.FactorizedRational

set_option backward.isDefEq.respectTransparency false

open Complex ComplexConjugate Real

variable {R : ℝ} {w : ℂ}

/-!
## Blaschke Factors

Given `R : ℝ` and `w : ℂ`, the Blaschke factor `Blaschke R w : ℂ → ℂ` is
meromorphic in normal form, has a single pole at `w`, no zeros, and takes values
of norm one on the circle of radius `R`.
-/

noncomputable def Blaschke (R : ℝ) (w : ℂ) : ℂ → ℂ :=
  fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w))

lemma meromorphicOn_blaschke (R : ℝ) (w : ℂ) :
    MeromorphicOn (Blaschke R w) Set.univ := by
  intro x hx
  unfold Blaschke
  fun_prop

lemma analyticOnNhd_blaschke (R : ℝ) (w : ℂ) (h : 0 < R) :
    AnalyticOnNhd ℂ (Blaschke R w) {w}ᶜ := by
  intro x hx
  have : ↑R * (x - w) ≠ 0 := mul_ne_zero (ne_zero_of_re_pos h) (sub_ne_zero_of_ne hx)
  unfold Blaschke
  fun_prop (disch := aesop)

lemma nonzero_blaschke {z : ℂ} (R : ℝ) (w : ℂ) (h : 0 < R) (hz : z ≠ w) (h₁ : ‖w‖ ≤ R) (h₂ : ‖z‖ ≤ R) :
    Blaschke R w z ≠ 0 := by
  -- Since $z \neq w$, the denominator $R(z - w)$ is non-zero. Also, from the given conditions, we know that $R^2 - \overline{w}z$ is not zero because if it were, then $\overline{w}z$ would equal $R^2$, which can't happen given the norms.
  have h_denom_ne_zero : R * (z - w) ≠ 0 := by
    exact mul_ne_zero ( Complex.ofReal_ne_zero.mpr h.ne' ) ( sub_ne_zero.mpr hz );
  -- Since $z \neq w$, the denominator $R(z - w)$ is non-zero. Also, from the given conditions, we know that $R^2 - \overline{w}z$ is not zero because if it were, then $\overline{w}z$ would equal $R^2$, which can't happen given the norms. Hence, $Blaschke R w z \neq 0$.
  have h_num_ne_zero : R^2 - (conj w) * z ≠ 0 := by
    contrapose! h_denom_ne_zero; simp_all +decide [ Complex.ext_iff, sq ] ;
    norm_num [ Complex.normSq, Complex.norm_def ] at *;
    rw [ Real.sqrt_le_iff ] at *;
    exact Or.inr ⟨ by nlinarith [ sq_nonneg ( w.re - z.re ), sq_nonneg ( w.im - z.im ) ], by nlinarith [ sq_nonneg ( w.re - z.re ), sq_nonneg ( w.im - z.im ) ] ⟩;
  exact div_ne_zero h_num_ne_zero h_denom_ne_zero

/-- The order is additive when multiplying meromorphic functions. -/
theorem meromorphicOrderAt_fun_mul {f g : ℂ → ℂ} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    meromorphicOrderAt (fun z ↦ f z * g z) x = meromorphicOrderAt f x + meromorphicOrderAt g x :=
  meromorphicOrderAt_smul hf hg

theorem meromorphicOrderAt_fun_inv {f : ℂ → ℂ} :
    meromorphicOrderAt (fun z ↦ (f z)⁻¹) x = -meromorphicOrderAt f x := by
  exact meromorphicOrderAt_inv

lemma order_blaschke (R : ℝ) (w : ℂ) (h : 0 < R) (h₂ : ‖w‖ ≠ R) :
    meromorphicOrderAt (Blaschke R w) w = -1 := by
  unfold Blaschke
  simp_rw [div_eq_mul_inv]
  rw [meromorphicOrderAt_fun_mul]
  have : meromorphicOrderAt (fun z ↦ ↑R ^ 2 - (starRingEnd ℂ) w * z) w = 0 := by
    refine (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff ?_).mpr ?_
    · apply AnalyticAt.meromorphicNFAt
      fun_prop
    · rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq w, sub_ne_zero]
      have : R ^ 2 ≠ ‖w‖ ^ 2 := by
        by_contra h₁
        rw [sq_eq_sq₀] at h₁
        grind
        exact h.le
        exact norm_nonneg w
      rwa [ne_eq, ← ofReal_pow, ofReal_inj]
  simp only [this, zero_add]
  clear this
  rw [meromorphicOrderAt_fun_inv]
  simp
  rw [meromorphicOrderAt_fun_mul]
  have : meromorphicOrderAt (fun z ↦ (R : ℂ)) w = 0 := by
    refine (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff ?_).mpr ?_
    · apply AnalyticAt.meromorphicNFAt
      fun_prop
    exact ne_zero_of_re_pos h
  rw [this, zero_add]
  clear this
  have : (1 : WithTop ℤ) = (1 : ℤ) := rfl
  rw [this, meromorphicOrderAt_eq_int_iff (n := 1)]
  use fun z ↦ 1
  constructor
  · fun_prop
  · constructor
    · exact one_ne_zero
    · filter_upwards
      aesop
  fun_prop
  fun_prop
  fun_prop
  fun_prop
  fun_prop

lemma meromorphicNFOn_blaschke (R : ℝ) (w : ℂ) (h : 0 < R) (h₂ : ‖w‖ ≠ R) :
    MeromorphicNFOn (Blaschke R w) Set.univ := by
  intro z hz
  by_cases h₁ : z = w
  · rw [meromorphicNFAt_iff_analyticAt_or]
    right
    use (meromorphicOn_blaschke R w z (Set.mem_univ z))
    constructor
    · simp_all only [Set.mem_univ, order_blaschke R w h h₂]
      exact sign_eq_neg_one_iff.mp rfl
    simp_all [Blaschke]
  apply (analyticOnNhd_blaschke R w h z h₁).meromorphicNFAt

lemma blaschke_eval_center (R : ℝ) (w : ℂ) :
    Blaschke R w w = 0 := by
  simp [Blaschke]

lemma blaschke_eval_circle_ne {z : ℂ} (R : ℝ) (w : ℂ) (h : 0 < R) (h₂ : ‖z‖ = R) (h₃ : z ≠ w) :
    ‖Blaschke R w z‖ = 1 := by
  -- By definition of Blaschke factor, we have ‖Blaschke R w z‖ = ‖(R² - conj w * z) / (R * (z - w))‖.
  simp [Blaschke];
  rw [ div_eq_iff ] <;> simp_all +decide [ Complex.normSq, Complex.norm_def ];
  · rw [ ← Real.sqrt_sq_eq_abs ];
    rw [ ← Real.sqrt_mul <| by positivity ]
    congr 1
    norm_cast
    rw [ ← h₂ ]
    rw [ Real.sq_sqrt <| by nlinarith ]
    ring;
  · exact ⟨ h.ne', ne_of_gt <| Real.sqrt_pos.mpr <| not_le.mp fun h' => h₃ <| by refine' Complex.ext _ _ <;> nlinarith ⟩

lemma log_blaschke_eval_circle {z : ℂ} (R : ℝ) (w : ℂ) (h : 0 < R) (h₂ : ‖z‖ = R) (h₃ : z ≠ w) :
    Real.log ‖Blaschke R w z‖ = 0 := by
  by_cases hz : z = w
  all_goals simp_all [blaschke_eval_circle_ne]
