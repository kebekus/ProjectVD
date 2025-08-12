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

theorem xx {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) 1)) :
    0 = 1 := by

  have CPS := cauchyPowerSeries f 0 1
  have IPS : FormalMultilinearSeries ℂ ℂ ℂ := by
    intro n
    by_cases n = 0
    · exact 0
    have := CPS (n - 1) (fun _ ↦ 1)
    apply ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (this / n)

  have := IPS.derivSeries




  have A := hf.hasFPowerSeriesOnBall one_pos

  have := A.hasSum (y := 0.5)

  have B := cauchyPowerSeries f 0 ↑1

  have := B 2 (fun _ ↦ 0)



  simp_all
  sorry
