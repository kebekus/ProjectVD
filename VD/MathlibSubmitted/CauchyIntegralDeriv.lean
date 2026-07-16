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

/--
Helper lemma for `hasDerivAt_circleIntegral_sub_inv_smul`: For `w ∈ ball c R`, there is a radius `d
> 0` such that `ball w d ⊆ ball c R` and all points of `ball w d` keep distance at least `d` from
the circle `sphere c R`.
-/
lemma exists_ball_subset_forall_le_norm_circleMap_sub (hw : w ∈ ball c R) :
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

/-!
## B1: Derivative of the Cauchy Integral in the Pole Parameter
-/

/--
**Derivative of the Cauchy integral**: if `g` is circle integrable and `w` lies inside the circle,
then the Cauchy-type integral `fun w ↦ ∮ z in C(c, R), (z - w)⁻¹ • g z` has derivative
`∮ z in C(c, R), ((z - w) ^ 2)⁻¹ • g z` at `w`.
-/
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
  · -- Measurability of the integrand, for `x` near `w`
    filter_upwards with x
    exact (Continuous.aestronglyMeasurable (by fun_prop)).smul
      ((Measurable.aestronglyMeasurable (by fun_prop)).smul hgm)
  · -- Integrability of the integrand at `w`
    have : CircleIntegrable ((fun z ↦ (z - w)⁻¹) • g) c R := by
      apply hg.smul_of_continuousOn
      apply ContinuousOn.inv₀ (by fun_prop)
      intro z hz
      apply sub_ne_zero.2
      intro h
      rw [mem_sphere, h, abs_of_pos hR] at hz
      rw [mem_ball] at hw
      exact absurd hz (ne_of_lt hw)
    simpa only [deriv_circleMap, Pi.smul_apply'] using this.out
  · -- Measurability of the differentiated integrand
    exact (Continuous.aestronglyMeasurable (by fun_prop)).smul
      ((Measurable.aestronglyMeasurable (by fun_prop)).smul hgm)
  · -- Uniform bound for the differentiated integrand near `w`
    filter_upwards with θ _ x hx
    rw [norm_smul, norm_smul, norm_inv, norm_pow, norm_mul, Complex.norm_I, mul_one,
      norm_circleMap_zero, abs_of_pos hR, ← mul_assoc]
    gcongr
    exact hdist x hx θ
  · -- Integrability of the bound
    exact (IntervalIntegrable.norm hg).const_mul _
  · -- Differentiability of the integrand in `x`, for `x` near `w`
    filter_upwards with θ _ x hx
    apply (HasDerivAt.smul_const _ (g (circleMap c R θ))).const_smul (circleMap 0 R θ * I)
    rw [show ((circleMap c R θ - x) ^ 2)⁻¹ = -(-1) / (circleMap c R θ - x) ^ 2 by simp]
    apply ((hasDerivAt_id' (x := x)).const_sub (circleMap c R θ)).inv
    exact sub_ne_zero.2 (circleMap_ne_mem_ball (hsub hx) θ)
