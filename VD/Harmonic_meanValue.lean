/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage
import VD.Harmonic_analytic2
import VD.ToMathlib.Analytic_meanValue

/-!
# The Mean Value Property of Complex Differentiable Functions
-/

open InnerProductSpace Metric Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℂ → ℝ} {c : ℂ} {R : ℝ}

theorem ContinuousLinearMap.circleAverage_comp_comm {ℓ : E →L[ℝ] F} {f : ℂ → E}
    (hf : CircleIntegrable f c R) :
    circleAverage (ℓ ∘ f) c R = ℓ (circleAverage f c R) := by
  unfold circleAverage
  rw [map_smul]
  congr
  apply ℓ.intervalIntegral_comp_comm hf


/--
The **Mean Value Property** of harmonic functions: If `f : ℂ → E` is harmonic in
a neighborhood of a closed disc of radius `R` and center `c`, then the circle
average `circleAverage f c R` equals `f c`.
-/
theorem circleAverage_of_harmonic
    (hf : HarmonicOnNhd f (closedBall c |R|)) (hR : 0 < R) :
    circleAverage f c R = f c := by

  obtain ⟨e, h₁e, h₂e⟩ := IsCompact.exists_thickening_subset_open (isCompact_closedBall c |R|)
    (isOpen_setOf_harmonicAt f) hf
  rw [thickening_closedBall h₁e (abs_nonneg R)] at h₂e
  obtain ⟨F, h₁F, h₂F⟩ := harmonic_is_realOfHolomorphic (add_pos_of_pos_of_nonneg h₁e (abs_nonneg R)) h₂e
  have h₃F : ∀ z ∈ closedBall c |R|, DifferentiableAt ℂ F z := by
    intro x hx
    have : x ∈ ball c (e + |R|) := by
      simp_all [lt_add_of_pos_of_le h₁e hx]
    have := h₁F x this
    fun_prop
  have := circleAverage_of_differentiable_on h₃F
  have t₀ : f = Complex.reCLM ∘ F := by
    sorry
  rw [t₀]
  rw [ContinuousLinearMap.circleAverage_comp_comm]
  simp_all
  refine ContinuousOn.circleIntegrable' ?_
  refine continuousOn_of_forall_continuousAt ?_
  intro x hx
  have : x ∈ closedBall c |R| := by sorry
  have := h₃F x this
  fun_prop
