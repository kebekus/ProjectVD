import VD.MeanValue
import VD.TrivialFunProp
import VD.TrivialIntervalCongruence

open Asymptotics Classical Complex ComplexConjugate Filter Function Metric Real Set Classical Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}

theorem testCase₁ {φ θ : ℝ} {r R : ℝ} (h₁ : 0 < r) (h₂ : r < R) :
    (R * exp (θ * I)) / (R * exp (θ * I)  - r * exp (φ * I))
      - (r * exp (θ * I)) / (r * exp (θ * I) - R * exp (φ * I))
    = ( (R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I)) ).re := by
  by_cases h₃ : ( R * Complex.exp ( θ * Complex.I ) - r * Complex.exp ( φ * Complex.I ) ) = 0
  <;> simp_all +decide [ Complex.ext_iff, div_eq_mul_inv ]
  · simp_all +decide [ sub_eq_iff_eq_add ]
    have := congr_arg ( · ^ 2 ) h₃.1
    have := congr_arg ( · ^ 2 ) h₃.2
    ring_nf at *
    nlinarith [ Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ ]
  · norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im ]
    ring_nf
    norm_cast
    norm_num [ Real.sin_sq, Real.cos_sq ]
    ring_nf
    norm_num

private lemma circleIntegrable₁ (hf : DiffContOnCl ℂ f (ball c |R|))
    (hw : w ∈ ball c |R|) (hR : 0 < R) :
    CircleIntegrable (fun z ↦ (z / (z - w)) • f z) c R := by
  apply ContinuousOn.circleIntegrable hR.le
  intro z hz
  have : z - w ≠ 0 := by
    by_contra h
    rw [abs_of_pos hR, sub_eq_zero] at *
    simp_all [dist_eq_norm]
  have : ContinuousWithinAt f (sphere c R) z := by
    apply hf.2.mono _ z hz
    rw [abs_of_pos hR, closure_ball c (ne_of_lt hR).symm]
    apply sphere_subset_closedBall
  fun_prop (disch := assumption)

/--
The integrand of circleAverage_of_differentiable_on₄ is actually integrable.
-/
theorem circleIntegrable₁₁ (hf : DiffContOnCl ℂ f (ball c |R|))
    (hw : w ∈ ball c |R|) :
    CircleIntegrable (fun z ↦ (z / (z - w)) • f z) c R := by
  rcases lt_trichotomy R 0 with (hR | hR | hR)
  · rw [circleIntegrable_congr_neg_radius]
    apply circleIntegrable₁ (by simpa) (by simpa) (by simpa)
  · simp_all
  · exact circleIntegrable₁ hf hw hR


theorem testCase₃ {φ θ : ℝ} {r R : ℝ} (h₁ : 0 < r) (h₂ : r < R) :
    ( (R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I)) ).re
    ≤ (R + r) / (R - r) := by
  rw [ div_eq_mul_inv ]
  -- Realize that $Real.cos(θ - φ) ≤ 1$, and thus $R^2 + r^2 - 2 * R * r * Real.cos(θ - φ) ≥ (R - r)^2$.
  have h_cos : (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) ≥ (R - r) ^ 2 := by
    nlinarith [ mul_pos h₁ ( sub_pos.mpr h₂ ), Real.cos_le_one ( θ - φ ) ]
  -- Substitute the simplified expression back into the inequality.
  have h_subst : (R^2 - r^2) / (R^2 + r^2 - 2 * R * r * Real.cos (θ - φ)) ≤ (R + r) / (R - r) := by
    rw [ div_le_div_iff₀ ]
    <;> nlinarith [ mul_pos h₁ ( sub_pos.mpr h₂ ) ]
  convert h_subst using 1
  norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im ]
  ring_nf
  norm_num [ Real.sin_sq, Real.cos_sq ]
  ring_nf
  rw [ Real.cos_sub ]
  ring

theorem testCase₄ {φ θ : ℝ} {r R : ℝ} (h₁ : 0 < r) (h₂ : r < R) :
    (R - r) / (R + r)
    ≤ ( (R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I)) ).re := by
  norm_num [ Complex.normSq, Complex.div_re ]
  rw [ ← add_div, div_le_div_iff₀ ]
  · ring_nf
    norm_num [ Real.sin_sq, Real.cos_sq ]
    ring_nf
    nlinarith [ mul_le_mul_of_nonneg_left
      ( show Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ ≤ 1 by nlinarith only [ sq_nonneg ( Real.cos θ * Real.sin φ - Real.sin θ * Real.cos φ ), Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ ] )
      ( show 0 ≤ R * r by nlinarith ), mul_le_mul_of_nonneg_left
        ( show Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ ≥ -1 by nlinarith only [ sq_nonneg ( Real.cos θ * Real.sin φ - Real.sin θ * Real.cos φ ), Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ ] )
        ( show 0 ≤ R * r by nlinarith ) ]
  · linarith
  · -- Expanding the squares and simplifying, we get:
    have h_expand : (R * Real.cos θ - r * Real.cos φ) * (R * Real.cos θ - r * Real.cos φ) + (R * Real.sin θ - r * Real.sin φ) * (R * Real.sin θ - r * Real.sin φ) = R^2 + r^2 - 2 * R * r * Real.cos (θ - φ) := by
      rw [ Real.cos_sub ]
      nlinarith [ Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ ]
    nlinarith [ mul_pos h₁ ( sub_pos.mpr h₂ ), Real.cos_le_one ( θ - φ ) ]

theorem circleAverage_of_differentiable_on₃ [CompleteSpace E]
    (hf : DiffContOnCl ℂ f (ball 0 |R|))
    (hw : w ∈ ball 0 R) (h₁w : w ≠ 0) (hR : 0 < R) :
    circleAverage (fun z ↦ ((z + w) / (z - w)).re • f z) 0 R = f w := by
  let W := R * exp (w.arg * I)
  let q := ‖w‖ / R
  have h₁q : 0 < q := div_pos (norm_pos_iff.mpr h₁w) hR
  have h₂q : q < 1 := by
    apply (div_lt_one hR).2
    rwa [mem_ball, dist_zero_right] at hw

  have η {x : ℂ} (h : ‖x‖ ≤ R) : q * x - W ≠ 0 := by
    by_cases h₁ : x = 0
    · aesop
    · have : ‖q * x‖ < ‖W‖ := by
        calc ‖q * x‖
          _ = ‖q‖ * ‖x‖ := by
            rw [Complex.norm_mul, norm_real, norm_eq_abs]
          _ < ‖x‖ := by
            rw [norm_eq_abs, abs_of_pos h₁q]
            apply (mul_lt_iff_lt_one_left _).2 h₂q
            aesop
          _ ≤ ‖W‖ := by
            simp_all [W, abs_of_pos hR]
      grind

  calc circleAverage (fun z ↦ ((z + w) / (z - w)).re • f z) 0 R
    _ = circleAverage (fun z ↦ (z / (z - w) - (q • z) / (q • z - W)) • f z) 0 R := by
      unfold q
      unfold W
      apply circleAverage_congr_sphere
      intro z hz
      simp only [real_smul, ofReal_div]
      match_scalars
      simp only [coe_algebraMap, mul_one]
      have h₁φ : R * exp (z.arg * I) = z := by
        convert norm_mul_exp_arg_mul_I z
        simp_all [abs_of_pos]
      rw [← norm_mul_exp_arg_mul_I w, ← h₁φ, ← testCase₁ (norm_pos_iff.mpr h₁w) (mem_ball_zero_iff.mp hw),
        norm_mul_exp_arg_mul_I w]
      congr 1
      ring_nf
      field [hR.ne.symm]
    _ = circleAverage (fun z ↦ (z / (z - w)) • f z) 0 R
        - circleAverage (fun z ↦ ((q • z) / (q • z - W)) • f z) 0 R := by
      simp_rw [sub_smul]
      rw [circleAverage_fun_sub]
      · -- CircleIntegrable (fun z ↦ (z / (z - w)) • f z) 0 R
        rw [← abs_of_pos hR] at hf hw
        apply circleIntegrable₁ _ hw hR
        rwa [abs_abs] at hf
      · -- CircleIntegrable (fun z ↦ (q • z / (q • z - W)) • f z) 0 R
        apply ContinuousOn.circleIntegrable'
        intro z hz
        have : ‖z‖ ≤ R := by
            rw [mem_sphere_iff_norm, sub_zero, abs_of_pos hR] at hz
            apply le_of_eq hz
        have : ContinuousWithinAt f (sphere 0 |R|) z := by
          apply hf.2.mono _ z hz
          rw [abs_of_pos hR, closure_ball 0 (ne_of_lt hR).symm]
          apply sphere_subset_closedBall
        fun_prop (disch := aesop)
    _ = f w - circleAverage (fun z ↦ ((q • z) / (q • z - W)) • f z) 0 R := by
      rw [← abs_of_pos hR] at hw
      simp [← circleAverage_sub_sub_inv_smul_of_differentiable_on hf hw]
    _ = f w := by
      simp [circleAverage_eq_circleIntegral (ne_of_lt hR).symm]
      have : ∮ (z : ℂ) in C(0, R), z⁻¹ • ((q * z) / (q * z - W)) • f z
          = ∮ (z : ℂ) in C(0, R), (q / (q * z - W)) • f z := by
        apply circleIntegral.integral_congr hR.le
        intro z hz
        match_scalars
        field [(by aesop: z ≠ 0)]
      rw [this]
      apply DiffContOnCl.circleIntegral_eq_zero hR.le
      apply DiffContOnCl.smul
      · constructor
        · intro x hx
          have : ‖x‖ ≤ R := by
            simp at hx
            exact hx.le
          have := η this
          fun_prop (disch := assumption)
        · intro x hx
          have : ‖x‖ ≤ R := by
            rw [closure_ball _ (ne_of_lt hR).symm] at hx
            simp at hx
            exact hx
          have := η this
          fun_prop (disch := assumption)
      · rwa [← abs_of_pos hR]

/-
theorem circleAverage_of_differentiable_on₄ [CompleteSpace E]
    --(h : DiffContOnCl ℂ f (ball c |R|))
    (hf : ∀ z ∈ closedBall 0 |R|, DifferentiableAt ℂ f z)
    (hw : w ∈ ball 0 |R|) :
    circleAverage (fun z ↦ ((z + w) / (z - w)).re • f z) 0 R = f w := by
  by_cases hR : R = 0
  · subst hR
    simp_all
  by_cases hW : w = 0
  · subst hW
    simp
  rcases gt_trichotomy R 0
  · sorry
  · sorry
  · sorry



  by_cases h₁w : w = 0
  · simp [h₁w]
  sorry
-/
