import VD.MathlibSubmitted.ComplexMeanvalue

open Asymptotics Classical Complex ComplexConjugate Filter Function Metric Real Set Classical Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}


theorem testCase₁ {φ θ : ℝ} {r R : ℝ} (h₁ : 0 < r) (h₂ : r < R) :
    (R * exp (θ * I)) / (R * exp (θ * I)  - r * exp (φ * I))
      - (r * exp (θ * I)) / (r * exp (θ * I) - R * exp (φ * I))
    = ( (R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I)) ).re := by
  by_cases h₃ : ( R * Complex.exp ( θ * Complex.I ) - r * Complex.exp ( φ * Complex.I ) ) = 0
  <;> simp_all +decide [ Complex.ext_iff, div_eq_mul_inv ];
  · simp_all +decide [ sub_eq_iff_eq_add ];
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

theorem circleAverage_of_differentiable_on₂ (hf : ∀ z ∈ closedBall 0 |R|, DifferentiableAt ℂ f z)
    (hw : w ∈ ball 0 |R|) (h₁w : w ≠ 0) (hR : 0 < R) :
    circleAverage (fun z ↦ ((z + w) / (z - w)).re • f z) 0 R = f w := by

  let r := ‖w‖
  let θ := w.arg
  let W := R * exp (θ * I)
  let q := r / R
  have h₁q : 0 < q := by sorry
  have h₂q : q < 1 := by sorry

  have :
      circleAverage (fun z ↦ (z / (z - w) - (q • z) / (q • z - W)) • f z) 0 R
      = circleAverage (fun z ↦ ((z + w) / (z - w)).re • f z) 0 R := by
    unfold q
    apply circleAverage_congr_sphere
    intro z hz
    simp
    match_scalars
    simp

    have h₁θ : r * exp (θ * I) = w := norm_mul_exp_arg_mul_I w
    rw [← h₁θ]
    let φ := z.arg
    have h₁φ : R * exp (φ * I) = z := by
      convert norm_mul_exp_arg_mul_I z
      simp_all [abs_of_pos]
    rw [← h₁φ, ← testCase₁]
    rw [h₁φ, h₁θ]
    congr 1
    rw [← h₁φ]
    ring_nf
    have : (r : ℂ) * (R : ℂ) * (R : ℂ)⁻¹ = r := by sorry
    rw [this]
    congr 3
    unfold W
    congr 2
    field
    aesop
    simp at hw
    rw [abs_of_pos hR] at hw
    exact hw

  rw [← this]
  simp_rw [sub_smul]
  rw [circleAverage_fun_sub]

  have :  circleAverage (fun z ↦ (z / (z - w)) • f z) 0 R = f w := by
    rw [← circleAverage_of_differentiable_on₁ hf hw]
    congr
    ext z
    aesop
    exact Ne.symm (ne_of_lt hR)
  simp [this]



  rw [circleAverage_eq_circleIntegral (ne_of_lt hR).symm]
  simp

  have : ∮ (z : ℂ) in C(0, R), z⁻¹ • ((q * z) / (q * z - W)) • f z
      = ∮ (z : ℂ) in C(0, R), (q / (q * z - W)) • f z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have : z ≠ 0 := by sorry
    simp_all
    match_scalars
    field
  rw [this]
  clear this

  apply DiffContOnCl.circleIntegral_eq_zero hR.le
  constructor
  · intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.smul
    · apply DifferentiableAt.div
      · fun_prop
      · fun_prop
      · rw [sub_ne_zero]
        simp at hx
        have : ‖q*x‖ < ‖W‖ := by
          by_cases h : x = 0
          · simp [h]
            aesop
          · calc ‖q*x‖
            _ = ‖q‖ * ‖x‖ := by
              aesop
            _ < ‖x‖ := by
              simp [abs_of_pos h₁q]
              refine (mul_lt_iff_lt_one_left ?_).mpr h₂q
              aesop
            _ ≤ ‖W‖ := by
              simp [W, abs_of_pos hR]
              exact hx.le
        grind
  · intro x hx
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.smul
    · apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · rw [sub_ne_zero]
        rw [closure_ball] at hx
        simp at hx
        have : ‖q*x‖ < ‖W‖ := by
          by_cases h : x = 0
          · simp [h]
            aesop
          · calc ‖q*x‖
            _ = ‖q‖ * ‖x‖ := by
              aesop
            _ < ‖x‖ := by
              simp [abs_of_pos h₁q]
              refine (mul_lt_iff_lt_one_left ?_).mpr h₂q
              aesop
            _ ≤ ‖W‖ := by
              simp [W, abs_of_pos hR]
              exact hx
        grind
        exact Ne.symm (ne_of_lt hR)
    · apply DifferentiableAt.continuousAt (𝕜 := ℂ)
      apply hf

      apply hf x
      sorry
  sorry
  sorry


theorem testCase₀ {φ θ : ℝ} {r R : ℝ} (h₁ : 0 < r) (h₂ : r < R) :
    ((R * exp (θ * I)) / (R * exp (θ * I)  - r * exp (φ * I))
      - (r * exp (θ * I)) / (r * exp (θ * I) - R * exp (φ * I))).im = 0 := by
  simp_all +decide [Complex.div_im]
  norm_num [Complex.normSq, Complex.exp_re, Complex.exp_im]
  ring_nf
  norm_num [Real.sin_sq, Real.cos_sq]
  ring

theorem testCase₃ {φ θ : ℝ} {r R : ℝ} (h₁ : 0 < r) (h₂ : r < R) :
    ( (R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I)) ).re
    ≤ (R + r) / (R - r) := by
  rw [ div_eq_mul_inv ];
  -- Realize that $Real.cos(θ - φ) ≤ 1$, and thus $R^2 + r^2 - 2 * R * r * Real.cos(θ - φ) ≥ (R - r)^2$.
  have h_cos : (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) ≥ (R - r) ^ 2 := by
    nlinarith [ mul_pos h₁ ( sub_pos.mpr h₂ ), Real.cos_le_one ( θ - φ ) ];
  -- Substitute the simplified expression back into the inequality.
  have h_subst : (R^2 - r^2) / (R^2 + r^2 - 2 * R * r * Real.cos (θ - φ)) ≤ (R + r) / (R - r) := by
    rw [ div_le_div_iff₀ ] <;> nlinarith [ mul_pos h₁ ( sub_pos.mpr h₂ ) ];
  convert h_subst using 1 ; norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im ] ; ring_nf ; norm_num [ Real.sin_sq, Real.cos_sq ] ; ring_nf;
  rw [ Real.cos_sub ] ; ring;

theorem testCase₄ {φ θ : ℝ} {r R : ℝ} (h₁ : 0 < r) (h₂ : r < R) :
    (R - r) / (R + r)
    ≤ ( (R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I)) ).re := by
  norm_num [ Complex.normSq, Complex.div_re ];
  rw [ ← add_div, div_le_div_iff₀ ];
  · ring_nf;
    norm_num [ Real.sin_sq, Real.cos_sq ] ; ring_nf;
    nlinarith [ mul_le_mul_of_nonneg_left ( show Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ ≤ 1 by nlinarith only [ sq_nonneg ( Real.cos θ * Real.sin φ - Real.sin θ * Real.cos φ ), Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ ] ) ( show 0 ≤ R * r by nlinarith ), mul_le_mul_of_nonneg_left ( show Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ ≥ -1 by nlinarith only [ sq_nonneg ( Real.cos θ * Real.sin φ - Real.sin θ * Real.cos φ ), Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ ] ) ( show 0 ≤ R * r by nlinarith ) ];
  · linarith;
  · -- Expanding the squares and simplifying, we get:
    have h_expand : (R * Real.cos θ - r * Real.cos φ) * (R * Real.cos θ - r * Real.cos φ) + (R * Real.sin θ - r * Real.sin φ) * (R * Real.sin θ - r * Real.sin φ) = R^2 + r^2 - 2 * R * r * Real.cos (θ - φ) := by
      rw [ Real.cos_sub ] ; nlinarith [ Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ ] ;
    nlinarith [ mul_pos h₁ ( sub_pos.mpr h₂ ), Real.cos_le_one ( θ - φ ) ]
