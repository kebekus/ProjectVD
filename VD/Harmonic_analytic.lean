/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.ToMathlib.Harmonic
import VD.ToMathlib.restrictScalars
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic


open Complex InnerProductSpace Topology

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : ℂ → ℝ} {x : ℂ}

/--
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 + I • ∂f/∂I` is complex
differentiable at `x`.
-/
theorem HarmonicAt.xx (hf : HarmonicAt f x) :
    DifferentiableAt ℂ (ofRealCLM ∘ (fderiv ℝ f · 1) + I • ofRealCLM ∘ (fderiv ℝ f · I)) x := by

  sorry
