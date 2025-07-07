/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.ToMathlib.Harmonic
import VD.ToMathlib.CauchyRiemann
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Complex InnerProductSpace Topology

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : ℂ → ℝ} {x : ℂ}

/--
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 - I • ∂f/∂I` is complex
differentiable at `x`.
-/
theorem HarmonicAt.xx (hf : HarmonicAt f x) :
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
    · sorry
    · have := hf.2
      sorry
    simp
    fun_prop
    repeat rw [fderiv_add]
    sorry
    sorry
