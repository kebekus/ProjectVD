/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage
import VD.ToMathlib.CauchyRiemann

/-!
# Mean Value Property of Harmonic Functions
-/

open Complex InnerProductSpace Real Topology

variable
  {f : ℂ → ℝ} {r : ℝ}

/-!
## Circle Averages as a Function of the Radius
-/

lemma continuousAt_circleAverage (h : ContDiffOn ℝ 0 f (Metric.sphere 0 r)) :
    ContinuousAt (circleAverage f 0) r := by
  unfold circleAverage
  apply ContinuousAt.mul (by fun_prop)
  sorry

lemma xx {r : ℝ} :
    DifferentiableAt ℝ (circleAverage f 0) r := by
  unfold circleAverage
  sorry
