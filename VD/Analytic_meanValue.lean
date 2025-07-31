/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage

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
  have ε : ℝ := by
    sorry
  have h₁ε : 0 < ε := by
    sorry
  have a : Set ℂ := Metric.closedBall 0 (r + ε) \ Metric.ball 0 (r - ε)
  have h₁a : IsCompact a := by
    sorry
  have h₂a : ∀ ρ t, a ∈ 𝓝 (circleMap 0 ρ t) := by
    sorry
  have n : Set ℝ := Metric.ball 0 (r + ε) \ Metric.closedBall 0 (r - ε)
  have hn : n ∈ 𝓝 r := by
    sorry
  have h₂n : ∀ ρ : ℝ, dist ρ r < ε → ∀ t : ℝ, circleMap 0 ρ t ∈ a := by
    sorry
  have h₂f : ContinuousOn f a := by
    sorry
  apply ContinuousAt.mul (by fun_prop)
  apply intervalIntegral.continuousAt_of_dominated_interval
  · apply Metric.eventually_nhds_iff.mpr
    use ε, h₁ε
    intro ρ hρ
    apply ContinuousOn.aestronglyMeasurable
    · intro t ht
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.comp' _ (by fun_prop)
      exact (continuousWithinAt_iff_continuousAt (h₂a ρ t)).1 (h₂f (circleMap 0 ρ t) (h₂n ρ hρ t))
    · exact measurableSet_uIoc
  ·
    sorry
  · sorry
  · sorry
  · sorry

lemma xx {r : ℝ} :
    DifferentiableAt ℝ (circleAverage f 0) r := by
  unfold circleAverage
  sorry
