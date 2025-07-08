/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import VD.ToMathlib.CauchyRiemann

/-!
# Analyticity of Harmonic Functions

If `f : ℂ → ℝ` is harmonic at `x`, we show that `∂f/∂1 - I • ∂f/∂I` is
complex-analytic at `x`.

TODO: As soon as PR #9598 (feat(Analysis/Complex): HasPrimitives on disc) is
merged, extend this to show that `f` itself is locally the real part of a
holomorphic function, and hence real-analytic.
-/

open Complex InnerProductSpace Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℂ → ℝ} {x : ℂ}

/--
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 - I • ∂f/∂I` is complex
differentiable at `x`.
-/
theorem HarmonicAt.differentiableAt_complex (hf : HarmonicAt f x) :
    DifferentiableAt ℂ (ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)) x := by
  have := hf.1
  apply differentiableAt_complex_iff_differentiableAt_real.2
  constructor
  · fun_prop
  · repeat rw [fderiv_add]
    repeat rw [fderiv_sub]
    repeat rw [fderiv_const_smul]
    repeat rw [fderiv_comp]
    simp
    repeat rw [mul_add]
    repeat rw [mul_sub]
    ring_nf
    simp
    rw [add_comm]
    rw [sub_eq_add_neg]
    congr 1
    · simp
      have : (fderiv ℝ (fun x ↦ (fderiv ℝ f x) 1) x) I = ((fderiv ℝ (fderiv ℝ f) x) 1) I := by
        congr


        sorry
      have := iteratedFDeriv_two_apply (𝕜 := ℝ) f x ![1, I]
      simp at this
      have t₀ : (fun x ↦ (fderiv ℝ f x) 1) = (fderiv ℝ (fderiv ℝ f) x) 1 := by
        sorry
      rw [← this]
      rw [← iteratedFDeriv_two_apply (𝕜 := ℝ) f x ![1, I] ]
      sorry
    · have := hf.2
      sorry
    simp
    all_goals fun_prop
