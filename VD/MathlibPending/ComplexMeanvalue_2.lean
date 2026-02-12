/-
Copyright (c) 2026 [Your Name]. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger
-/
import VD.MathlibSubmitted.MeanValue

open Complex Metric Real Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}

/--
Express arbitrary circle averages as circle averages centered at the origin.
-/
@[simp] lemma circleAverage_comp_add_right :
    circleAverage (fun z ↦ f (z - c)) c R = circleAverage f 0 R := by
  unfold circleAverage
  grind [← circleMap_sub_center]

/-!
# Poisson integral formula
-/

-- Version of `DiffContOnCl.circleAverage_re_smul` in case where the center of
-- the ball is zero.
private lemma DiffContOnCl.circleAverage_re_smul_on_ball_zero [CompleteSpace E]
    (hf : DiffContOnCl ℂ f (ball 0 R)) (hw : w ∈ ball 0 R) :
    circleAverage (fun z ↦ ((z + w) / (z - w)).re • f z) 0 R = f w := by
  -- Trivial case: nonpositive radius
  rcases le_or_gt R 0 with hR | hR
  · simp_all [(ball_eq_empty).2 hR]
  -- Trivial case: w is at the center
  by_cases h₁w : w = 0
  · subst w
    simp only [add_zero, sub_zero]
    have : EqOn (fun z ↦ (z / z).re • f z) f (sphere 0 |R|) := by
      intro z hz
      have : z ≠ 0 := by
        by_contra h
        simp_all [mem_sphere_iff_norm, sub_self, norm_zero, eq_comm, abs_eq_zero]
      simp [div_self this]
    rw [circleAverage_congr_sphere this]
    rw [← abs_of_pos hR] at hf
    apply circleAverage_of_differentiable_on_ hf
  -- General case: positive radius, w is not at the center
  let W := R * exp (w.arg * I)
  let q := ‖w‖ / R
  have h₁q : 0 < q := div_pos (norm_pos_iff.mpr h₁w) hR
  have h₂q : q < 1 := by
    apply (div_lt_one hR).2
    rwa [mem_ball, dist_zero_right] at hw
  -- Lemma used by automatisation tactics to ensure that quotients are non-zero.
  have η₀ {x : ℂ} (h : ‖x‖ ≤ R) : q * x - W ≠ 0 := by
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
  -- Trigonometric identity used in the computation, relating the integration
  -- kernel of the theorem to the integrand appearing in the classic mean value
  -- theorem.
  have η₁ {φ θ : ℝ} {r : ℝ} (h₁ : 0 < r) (h₂ : r < R) :
      (R * exp (θ * I)) / (R * exp (θ * I)  - r * exp (φ * I)) - (r * exp (θ * I)) / (r * exp (θ * I) - R * exp (φ * I))
      = ((R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I))).re := by
    by_cases h₃ : (R * exp ( θ * I ) - r * exp (φ * Complex.I)) = 0
    · simp_all only [mem_ball, dist_zero_right, Complex.ext_iff, zero_re, zero_im, not_and, ne_eq,
        sub_eq_iff_eq_add, zero_add, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, mul_im,
        add_zero, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, div_eq_mul_inv, add_re, inv_re, sub_re,
        sub_self, mul_zero, add_im, inv_im, sub_im, neg_zero, ofReal_zero, neg_sub]
      have := congr_arg ( · ^ 2 ) h₃.1
      have := congr_arg ( · ^ 2 ) h₃.2
      ring_nf at *
      nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]
    · simp_all only [mem_ball, dist_zero_right, Complex.ext_iff, zero_re, zero_im, not_and, ne_eq,
        sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, sub_im, mul_im, add_zero,
        exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, div_eq_mul_inv, add_re, inv_re, add_im, inv_im,
        neg_sub, ofReal_sub, ofReal_mul, ofReal_add, ofReal_cos, ofReal_inv, ofReal_sin,
        cos_ofReal_im, mul_zero, normSq_ofReal, mul_inv_rev, map_eq_zero, not_false_eq_true,
        implies_true, mul_inv_cancel_left₀, sub_self, neg_zero, sin_ofReal_im]
      norm_num [normSq, exp_re, exp_im]
      ring_nf
      norm_cast
      norm_num [Real.sin_sq, Real.cos_sq]
      ring_nf
      tauto
  -- Main computation starts here
  calc circleAverage (fun z ↦ ((z + w) / (z - w)).re • f z) 0 R
    _ = circleAverage (fun z ↦ (z / (z - w) - (q • z) / (q • z - W)) • f z) 0 R := by
      apply circleAverage_congr_sphere
      intro z hz
      match_scalars
      simp only [q, W, real_smul, ofReal_div, coe_algebraMap, mul_one]
      have h₁φ : R * exp (z.arg * I) = z := by
        convert norm_mul_exp_arg_mul_I z
        simp_all [abs_of_pos]
      rw [← norm_mul_exp_arg_mul_I w, ← h₁φ, ← η₁ (norm_pos_iff.mpr h₁w) (mem_ball_zero_iff.mp hw),
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
        apply ContinuousOn.circleIntegrable hR.le
        intro z hz
        have : z - w ≠ 0 := by
          by_contra h
          rw [abs_of_pos hR, sub_eq_zero] at *
          simp_all [dist_eq_norm]
        have : ContinuousWithinAt f (sphere 0 R) z := by
          apply hf.2.mono _ z hz
          rw [abs_of_pos hR, closure_ball 0 (ne_of_lt hR).symm]
          apply sphere_subset_closedBall
        fun_prop (disch := assumption)
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
      rw [← abs_of_pos hR] at hw hf
      simp [← circleAverage_sub_sub_inv_smul_of_differentiable_on_ hf hw]
    _ = f w := by
      simp only [real_smul, circleAverage_eq_circleIntegral (ne_of_lt hR).symm, mul_inv_rev, inv_I,
        neg_mul, sub_zero, neg_smul, sub_neg_eq_add, add_eq_left, isUnit_iff_ne_zero, ne_eq,
        mul_eq_zero, I_ne_zero, inv_eq_zero, ofReal_eq_zero, pi_ne_zero, OfNat.ofNat_ne_zero,
        or_self, not_false_eq_true, IsUnit.smul_eq_zero]
      have : ∮ (z : ℂ) in C(0, R), z⁻¹ • ((q * z) / (q * z - W)) • f z
          = ∮ (z : ℂ) in C(0, R), (q / (q * z - W)) • f z := by
        apply circleIntegral.integral_congr hR.le
        intro z hz
        match_scalars
        field [(by aesop: z ≠ 0)]
      rw [this]
      apply DiffContOnCl.circleIntegral_eq_zero hR.le
      -- DiffContOnCl ℂ (fun z ↦ (↑q / (↑q * z - W)) • f z) (ball 0 R)
      apply DiffContOnCl.smul _ hf
      · constructor
        · intro x hx
          have : ‖x‖ ≤ R := by
            rw [mem_ball, dist_zero_right] at hx
            exact hx.le
          have := η₀ this
          fun_prop (disch := assumption)
        · intro x hx
          have : ‖x‖ ≤ R := by
            rwa [closure_ball _ (ne_of_lt hR).symm, mem_closedBall, dist_zero_right] at hx
          have := η₀ this
          fun_prop (disch := assumption)

/--
**Poisson integral formula** for ℂ-differentiable functions on arbitrary disks
in the complex plane, formulated with the real part of the Herglotz–Riesz kernel
of integration.
-/
theorem DiffContOnCl.circleAverage_re_smul [CompleteSpace E] {c : ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    circleAverage (fun z ↦ ((z - c + (w - c)) / ((z - c) - (w - c))).re • f z) c R = f w := by
  rcases le_or_gt R 0 with hR | hR
  · simp_all [(ball_eq_empty).2 hR]
  have h₁g : DiffContOnCl ℂ (fun z ↦ f (z + c)) (ball 0 R) :=
    ⟨hf.1.comp (by fun_prop) (fun z hz ↦ by aesop),
      hf.2.comp (by fun_prop) (fun z hz ↦ by simp_all [closure_ball _ (ne_of_lt hR).symm])⟩
  have h₂g : w - c ∈ ball 0 R := by simpa using hw
  simpa [← circleAverage_comp_add_right (c := c)]
    using circleAverage_re_smul_on_ball_zero h₁g h₂g

/--
**Poisson integral formula** for ℂ-differentiable functions on arbitrary disks
in the complex plane, formulated with the Poisson kernel of integration.
-/
theorem DiffContOnCl.circleAverage_div_smul [CompleteSpace E] {c : ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    circleAverage (fun z ↦ ((‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2) • f z) c R
      = f w := by
  rw [← hf.circleAverage_re_smul hw]
  apply circleAverage_congr_sphere
  intro z hz
  have {a b : ℂ} :
      ((a + b) / (a - b)).re = (‖a‖ ^ 2 - ‖b‖ ^ 2) / ‖a - b‖ ^ 2 := by
    rw [div_re, normSq_eq_norm_sq (a - b)]
    calc (a + b).re * (a - b).re / ‖a - b‖ ^ 2 + (a + b).im * (a - b).im / ‖a - b‖ ^ 2
      _ = ((a.re + b.re) * (a.re - b.re) + (a.im + b.im) * (a.im - b.im)) / ‖a - b‖ ^ 2 := by
        simp only [add_re, sub_re, add_im, sub_im, add_div]
      _ = ((a.re * a.re + a.im * a.im) - (b.re * b.re + b.im * b.im)) / ‖a - b‖ ^ 2 := by
        ring_nf
      _ = ((normSq a) - (normSq b)) / ‖a - b‖ ^ 2 := by
        simp only [normSq_apply]
      _ = (‖a‖ ^ 2 - ‖b‖ ^ 2) / ‖a - b‖ ^ 2 := by
        simp only [normSq_eq_norm_sq]
  simp_rw [this]
