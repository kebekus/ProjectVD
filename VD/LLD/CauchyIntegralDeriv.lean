/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Derivative of the Cauchy Integral — LLD work packages B1–B3

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §4.

Mathlib target: extend `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`
(and/or `Mathlib/Analysis/Complex/Poisson.lean`).
Dependencies: none (independently PR-able).

For a merely circle-integrable function `g`, this file differentiates Cauchy-type integrals with
respect to the pole parameter.

- `hasDerivAt_circleIntegral_sub_inv_smul` (B1): for `w` inside the circle, the Cauchy-type
  integral `fun w ↦ ∮ z in C(c, R), (z - w)⁻¹ • g z` has derivative
  `∮ z in C(c, R), ((z - w) ^ 2)⁻¹ • g z` at `w`. This complements
  `hasFPowerSeriesOn_cauchy_integral`, which gives analyticity but not this closed form at
  off-center points.

- `hasDerivAt_circleAverage_herglotzRieszKernel_smul` (B2): the analogous statement for the
  Herglotz–Riesz kernel integral `fun w ↦ circleAverage (herglotzRieszKernel 0 w • g) 0 R`, whose
  derivative is `circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • g ζ) 0 R`. Corollaries record
  differentiability and analyticity in `w` on the ball.

- `re_circleAverage_herglotzRieszKernel_smul` (B3): for real-valued `g`, taking real parts
  commutes with the Herglotz–Riesz kernel integral.

All proofs of the derivative formulas run through
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` over `𝕜 = ℂ`: on a small ball
`ball w d` whose closure stays inside `ball c R`, the differentiated integrands are dominated by
an integrable bound of the form `C * ‖g (circleMap c R θ)‖`.
-/

open Complex Filter MeasureTheory Metric Real Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {c w : ℂ} {R : ℝ} {g : ℂ → E}

/-!
## Auxiliary Lemmas
-/

/-- For `w ∈ ball c R`, there is a radius `d > 0` such that `ball w d ⊆ ball c R` and all points
of `ball w d` keep distance at least `d` from the circle `sphere c R`. -/
private lemma exists_ball_subset_forall_le_norm_circleMap_sub (hw : w ∈ ball c R) :
    ∃ d > 0, ball w d ⊆ ball c R ∧ ∀ x ∈ ball w d, ∀ θ : ℝ, d ≤ ‖circleMap c R θ - x‖ := by
  have hR : 0 < R := pos_of_mem_ball hw
  rw [mem_ball] at hw
  refine ⟨(R - dist w c) / 2, by linarith, fun x hx ↦ ?_, fun x hx θ ↦ ?_⟩ <;>
    rw [mem_ball] at hx
  · rw [mem_ball]
    have := dist_triangle x w c
    linarith
  · have h₁ : dist (circleMap c R θ) c = R := by
      simpa [abs_of_pos hR] using mem_sphere.1 (circleMap_mem_sphere' c R θ)
    have h₂ := dist_triangle (circleMap c R θ) x c
    have h₃ := dist_triangle x w c
    rw [← dist_eq_norm]
    linarith

/-- The Herglotz–Riesz kernel `herglotzRieszKernel c w` is continuous on the circle
`sphere c |R|` whenever `w ∈ ball c R`. -/
private lemma continuousOn_herglotzRieszKernel_sphere (hw : w ∈ ball c R) :
    ContinuousOn (herglotzRieszKernel c w) (sphere c |R|) := by
  have hR : 0 < R := pos_of_mem_ball hw
  rw [herglotzRieszKernel_fun_def]
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro z hz
  rw [sub_sub_sub_cancel_right]
  apply sub_ne_zero.2
  intro h
  rw [mem_sphere, h, abs_of_pos hR] at hz
  rw [mem_ball] at hw
  exact absurd hz (ne_of_lt hw)

/-!
## B1: Derivative of the Cauchy Integral in the Pole Parameter
-/

/-- **Derivative of the Cauchy integral**: if `g` is circle integrable and `w` lies inside the
circle, then the Cauchy-type integral `fun w ↦ ∮ z in C(c, R), (z - w)⁻¹ • g z` has derivative
`∮ z in C(c, R), ((z - w) ^ 2)⁻¹ • g z` at `w`. -/
theorem hasDerivAt_circleIntegral_sub_inv_smul [CompleteSpace E]
    (hg : CircleIntegrable g c R) (hw : w ∈ ball c R) :
    HasDerivAt (fun w ↦ ∮ z in C(c, R), (z - w)⁻¹ • g z)
      (∮ z in C(c, R), ((z - w) ^ 2)⁻¹ • g z) w := by
  have hR : 0 < R := pos_of_mem_ball hw
  obtain ⟨d, hd, hsub, hdist⟩ := exists_ball_subset_forall_le_norm_circleMap_sub hw
  have hgm : AEStronglyMeasurable (fun θ ↦ g (circleMap c R θ))
      (volume.restrict (uIoc 0 (2 * π))) := (intervalIntegrable_iff.1 hg).aestronglyMeasurable
  simp only [circleIntegral, deriv_circleMap]
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x θ ↦ (circleMap 0 R θ * I) • ((circleMap c R θ - x) ^ 2)⁻¹ • g (circleMap c R θ))
    (bound := fun θ ↦ R * (d ^ 2)⁻¹ * ‖g (circleMap c R θ)‖)
    (ball_mem_nhds w hd) ?_ ?_ ?_ ?_ ?_ ?_).2
  -- Measurability of the integrand, for `x` near `w`
  · filter_upwards with x
    exact (Continuous.aestronglyMeasurable (by fun_prop)).smul
      ((Measurable.aestronglyMeasurable (by fun_prop)).smul hgm)
  -- Integrability of the integrand at `w`
  · have h₁ : ContinuousOn (fun z ↦ (z - w)⁻¹) (sphere c |R|) := by
      apply ContinuousOn.inv₀ (by fun_prop)
      intro z hz
      apply sub_ne_zero.2
      intro h
      rw [mem_sphere, h, abs_of_pos hR] at hz
      rw [mem_ball] at hw
      exact absurd hz (ne_of_lt hw)
    have h₂ : CircleIntegrable ((fun z ↦ (z - w)⁻¹) • g) c R := hg.smul_of_continuousOn h₁
    simpa only [deriv_circleMap, Pi.smul_apply'] using h₂.out
  -- Measurability of the differentiated integrand
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).smul
      ((Measurable.aestronglyMeasurable (by fun_prop)).smul hgm)
  -- Uniform bound for the differentiated integrand near `w`
  · filter_upwards with θ _ x hx
    rw [norm_smul, norm_smul, norm_inv, norm_pow, norm_mul, Complex.norm_I, mul_one,
      norm_circleMap_zero, abs_of_pos hR, ← mul_assoc]
    gcongr
    exact hdist x hx θ
  -- Integrability of the bound
  · exact (IntervalIntegrable.norm hg).const_mul _
  -- Differentiability of the integrand in `x`, for `x` near `w`
  · filter_upwards with θ _ x hx
    have h₁ : circleMap c R θ - x ≠ 0 := sub_ne_zero.2 (circleMap_ne_mem_ball (hsub hx) θ)
    have h₂ : HasDerivAt (fun x : ℂ ↦ (circleMap c R θ - x)⁻¹)
        (((circleMap c R θ - x) ^ 2)⁻¹) x := by
      have h₃ := ((hasDerivAt_id' (x := x)).const_sub (circleMap c R θ)).inv h₁
      rw [show -(-1 : ℂ) / (circleMap c R θ - x) ^ 2 = ((circleMap c R θ - x) ^ 2)⁻¹ by
        rw [neg_neg, one_div]] at h₃
      exact h₃
    exact (h₂.smul_const (g (circleMap c R θ))).const_smul (circleMap 0 R θ * I)

/-!
## B2: Derivative of the Herglotz–Riesz Kernel Integral
-/

/-- **Derivative of the Herglotz–Riesz kernel integral**: if `g` is circle integrable and `w`
lies inside the circle, then `fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • g ζ) 0 R`
has derivative `circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • g ζ) 0 R` at `w`. -/
theorem hasDerivAt_circleAverage_herglotzRieszKernel_smul [CompleteSpace E]
    (hg : CircleIntegrable g 0 R) (hw : w ∈ ball 0 R) :
    HasDerivAt (fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • g ζ) 0 R)
      (circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • g ζ) 0 R) w := by
  have hR : 0 < R := pos_of_mem_ball hw
  obtain ⟨d, hd, hsub, hdist⟩ := exists_ball_subset_forall_le_norm_circleMap_sub hw
  have hgm : AEStronglyMeasurable (fun θ ↦ g (circleMap 0 R θ))
      (volume.restrict (uIoc 0 (2 * π))) := (intervalIntegrable_iff.1 hg).aestronglyMeasurable
  simp only [circleAverage_def]
  apply HasDerivAt.const_smul
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x θ ↦ (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) • g (circleMap 0 R θ))
    (bound := fun θ ↦ 2 * R * (d ^ 2)⁻¹ * ‖g (circleMap 0 R θ)‖)
    (ball_mem_nhds w hd) ?_ ?_ ?_ ?_ ?_ ?_).2
  -- Measurability of the integrand, for `x` near `w`
  · filter_upwards with x
    apply AEStronglyMeasurable.smul _ hgm
    simp only [herglotzRieszKernel_def, sub_zero]
    exact Measurable.aestronglyMeasurable (by fun_prop)
  -- Integrability of the integrand at `w`
  · have h₁ : CircleIntegrable (herglotzRieszKernel 0 w • g) 0 R :=
      hg.smul_of_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)
    simpa only [CircleIntegrable, Pi.smul_apply'] using h₁
  -- Measurability of the differentiated integrand
  · exact (Measurable.aestronglyMeasurable (by fun_prop)).smul hgm
  -- Uniform bound for the differentiated integrand near `w`
  · filter_upwards with θ _ x hx
    have h₁ : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [norm_smul, norm_div, norm_mul, norm_circleMap_zero, abs_of_pos hR, norm_pow,
      div_eq_mul_inv, h₁]
    gcongr
    exact hdist x hx θ
  -- Integrability of the bound
  · exact (IntervalIntegrable.norm hg).const_mul _
  -- Differentiability of the integrand in `x`, for `x` near `w`
  · filter_upwards with θ _ x hx
    have h₁ : circleMap 0 R θ - x ≠ 0 := sub_ne_zero.2 (circleMap_ne_mem_ball (hsub hx) θ)
    have h₂ : HasDerivAt (fun x ↦ herglotzRieszKernel 0 x (circleMap 0 R θ))
        (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) x := by
      have h₃ := ((hasDerivAt_id' (x := x)).const_add (circleMap 0 R θ)).div
        ((hasDerivAt_id' (x := x)).const_sub (circleMap 0 R θ)) h₁
      simp only [herglotzRieszKernel_def, sub_zero]
      rw [show (1 * (circleMap 0 R θ - x) - (circleMap 0 R θ + x) * -1)
          = 2 * circleMap 0 R θ by ring] at h₃
      exact h₃
    exact h₂.smul_const (g (circleMap 0 R θ))

/-- The Herglotz–Riesz kernel integral of a circle-integrable function is differentiable in the
pole parameter, throughout the open ball. -/
theorem differentiableOn_circleAverage_herglotzRieszKernel_smul [CompleteSpace E]
    (hg : CircleIntegrable g 0 R) :
    DifferentiableOn ℂ
      (fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • g ζ) 0 R) (ball 0 R) :=
  fun _ hw ↦
    (hasDerivAt_circleAverage_herglotzRieszKernel_smul hg
      hw).differentiableAt.differentiableWithinAt

/-- The Herglotz–Riesz kernel integral of a circle-integrable function is analytic in the pole
parameter, throughout the open ball. -/
theorem analyticOnNhd_circleAverage_herglotzRieszKernel_smul [CompleteSpace E]
    (hg : CircleIntegrable g 0 R) :
    AnalyticOnNhd ℂ
      (fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • g ζ) 0 R) (ball 0 R) :=
  (differentiableOn_circleAverage_herglotzRieszKernel_smul hg).analyticOnNhd isOpen_ball

/-!
## B3: Real Part of the Herglotz–Riesz Kernel Integral
-/

/-- Taking real parts commutes with the Herglotz–Riesz kernel integral of a real-valued
circle-integrable function. -/
theorem re_circleAverage_herglotzRieszKernel_smul {g : ℂ → ℝ}
    (hg : CircleIntegrable g 0 R) (hw : w ∈ ball 0 R) :
    (circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 R).re
      = circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 R := by
  have h₁ : CircleIntegrable (fun ζ ↦ (g ζ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg ⊢
    exact Complex.ofRealCLM.integrable_comp hg
  have h₂ : CircleIntegrable (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 R :=
    h₁.smul_of_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)
  calc (circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 R).re
      = Complex.reCLM (circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 R) := rfl
    _ = circleAverage (Complex.reCLM ∘ fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 R :=
        (Complex.reCLM.circleAverage_comp_comm h₂).symm
    _ = circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 R := by
        congr 1
        funext ζ
        simp [Complex.mul_re]
