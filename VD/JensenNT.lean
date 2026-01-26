import Mathlib.Analysis.Complex.MeanValue

open Asymptotics Complex Filter Function Metric Real Set Classical Topology


/-
# Replacement of Mathlib.Analysis.Complex.MeanValue
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}

-- Helper lemma: proof of `circleAverage_of_differentiable_on_off_countable` in case `0 < R`.
private theorem circleAverage_of_differentiable_on_off_countable_posRadius' (hR : 0 < R)
    (hs : s.Countable) (h₁f : ContinuousOn f (closedBall c R))
    (h₂f : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) (hw : w ∈ ball c R) :
    circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R = f w := by
  calc circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R
  _ = (2 * π * I)⁻¹ • (∮ z in C(c, R), (z - w)⁻¹ • f z) := by
    simp [circleAverage_eq_circleIntegral hR.ne']
    apply circleIntegral.integral_congr hR.le
    intro z hz
    match_scalars
    have : z - c ≠ 0 := by aesop
    grind
  _ = f w := by
    rw [circleIntegral_sub_inv_smul_of_differentiable_on_off_countable hs hw h₁f h₂f]
    match_scalars
    simp [field]

theorem circleAverage_of_differentiable_on_off_countable' (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : ∀ z ∈ ball c |R| \ s, DifferentiableAt ℂ f z)
    (hw : w ∈ ball c |R|) (hR : R ≠ 0) :
    circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R = f w := by
  rcases lt_trichotomy 0 R with h | rfl | h
  · rw [← abs_of_pos h]
    exact circleAverage_of_differentiable_on_off_countable_posRadius' (abs_pos_of_pos h) hs h₁f h₂f hw
  · tauto
  · rw [← circleAverage_neg_radius, ← abs_of_neg h]
    exact circleAverage_of_differentiable_on_off_countable_posRadius' (abs_pos_of_neg h) hs h₁f h₂f hw

theorem circleAverage_of_differentiable_on_off_countable₀ (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : ∀ z ∈ ball c |R| \ s, DifferentiableAt ℂ f z) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp [hR]
  · rw [← circleAverage_of_differentiable_on_off_countable' hs h₁f h₂f (by aesop) hR]
    apply circleAverage_congr_sphere
    intro z hz
    have : z - c ≠ 0 := by grind only [ne_of_mem_sphere, = abs.eq_1, = max_def]
    simp_all

theorem circleAverage_of_differentiable_on' (hf : ∀ z ∈ closedBall c |R|, DifferentiableAt ℂ f z)
    (hw : w ∈ ball c |R|) (hR : R ≠ 0) :
    circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R = f w :=
  circleAverage_of_differentiable_on_off_countable' countable_empty
    (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt)
    (fun z hz ↦ hf z (by simp_all [le_of_lt])) hw hR

theorem circleAverage_of_differentiable_on₀ (hf : ∀ z ∈ closedBall c |R|, DifferentiableAt ℂ f z) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp [hR]
  · rw [← circleAverage_of_differentiable_on' hf (by aesop) hR]
    apply circleAverage_congr_sphere
    intro z hz
    have : z - c ≠ 0 := by grind only [ne_of_mem_sphere, = abs.eq_1, = max_def]
    simp_all

--
