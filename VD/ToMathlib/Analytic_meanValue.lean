/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The Mean Value Property of Complex Differentiable Functions
-/

open Complex Metric Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {R : ℝ} {c : ℂ} {s : Set ℂ}

/--
Expression of the circleAverage in terms of a circleIntegral.
-/
theorem circleAverage_eq_circleIntegral (h : R ≠ 0) :
    circleAverage f c R = (2 * π * I)⁻¹ • (∮ (z : ℂ) in C(c, R), (z - c)⁻¹ • f z) := by
  calc circleAverage f c R
  _ = (2 * π : ℂ)⁻¹ • ∫ (θ : ℝ) in 0..2 * π, f (circleMap c R θ) := by
    unfold circleAverage
    simp [← coe_smul]
  _ = (2 * π * I)⁻¹ • ∫ (θ : ℝ) in 0..2 * π, I • f (circleMap c R θ) := by
    rw [intervalIntegral.integral_smul, ← smul_assoc]
    congr
    rw [smul_eq_mul]
    nth_rw 2 [mul_inv_rev]
    nth_rw 3 [mul_comm]
    rw [mul_assoc]
    aesop
  _ = (2 * π * I)⁻¹ • (∮ (z : ℂ) in C(c, R), (z - c)⁻¹ • f z) := by
    unfold circleIntegral
    congr
    ext θ
    simp [deriv_circleMap, circleMap_sub_center]
    rw [← smul_assoc]
    congr
    rw [smul_eq_mul, mul_comm, ← mul_assoc, right_eq_mul₀ I_ne_zero]
    apply inv_mul_cancel₀ (circleMap_ne_center h)

-- Helper lemma: proof of `circleAverage_of_differentiable_on_off_countable` in case `0 < R`.
private theorem circleAverage_of_differentiable_on_off_countable_posRadius [CompleteSpace E]
    (hR : 0 < R)
    (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c R))
    (h₂f : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    circleAverage f c R = f c := by
  calc circleAverage f c R
  _ = (2 * π * I)⁻¹ • (∮ (z : ℂ) in C(c, R), (z - c)⁻¹ • f z) := by
    rw [circleAverage_eq_circleIntegral]
    exact (ne_of_lt hR).symm
  _ = f c := by
    rw [circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable hR hs h₁f h₂f, ← smul_assoc]
    nth_rw 2 [((MulAction.one_smul (f c)).symm : f c = (1 : ℂ) • f c)]
    congr
    rw [smul_eq_mul]
    apply inv_mul_cancel₀ two_pi_I_ne_zero

/--
The **Mean Value Property** of complex differentiable functions: If `f : ℂ → E`
is continuous on a closed disc of radius `R` and center `c`, and is complex
differentiable at all but countably many points of its interior, then the circle
average `circleAverage f c R` equals `f c`.
-/
theorem circleAverage_of_differentiable_on_off_countable [CompleteSpace E]
    (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c |R|))
    (h₂f : ∀ z ∈ ball c |R| \ s, DifferentiableAt ℂ f z) :
    circleAverage f c R = f c := by
  rcases lt_trichotomy 0 R with h|h|h
  · rw [← abs_of_pos h]
    exact circleAverage_of_differentiable_on_off_countable_posRadius (abs_pos_of_pos h) hs h₁f h₂f
  · simp [h.symm]
  · rw [← circleAverage_neg_radius, ← abs_of_neg h]
    exact circleAverage_of_differentiable_on_off_countable_posRadius (abs_pos_of_neg h) hs h₁f h₂f

/--
The **Mean Value Property** of complex differentiable functions: If `f : ℂ → E`
is complex differentiable at all points of a closed disc of radius `R` and
center `c`, then the circle average `circleAverage f c R` equals `f c`.
-/
theorem circleAverage_of_differentiable_on [CompleteSpace E]
    (hf : ∀ z ∈ closedBall c |R|, DifferentiableAt ℂ f z) :
    circleAverage f c R = f c := by
  apply circleAverage_of_differentiable_on_off_countable Set.countable_empty
  · exact fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  · intro z hz
    apply hf z
    simp_all [le_of_lt]
