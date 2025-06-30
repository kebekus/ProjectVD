/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import VD.cauchyRiemann

/-!
# Holomorphic Function

This file introduces holomorphic functions as a convenience notation for
functions that are complex differentiable in a neighborhood of a point.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

open Topology

/--
A function between normed complex vector spaces is holomorphic at `x` if it is
complex differentiable in a neighborhoof of `x`.
-/
def HolomorphicAt (f : E → F) (x : E) : Prop :=
  ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ f z

/--
A function on `ℂ` is holomorphic at `x` if it is continuously differentiable at
`x`.
-/
theorem holomorphicAt_iff_contDiffAt {f : ℂ → F} {x : ℂ} :
    HolomorphicAt f x ↔ ContDiffAt ℂ 1 f x := by
  sorry

/--
A function from `ℂ` to a complete space is holomorphic at `x` if it is
analytic at `x`.
-/
theorem holomorphicAt_iff_AnalyticAt [CompleteSpace F] {f : ℂ → F} {x : ℂ} :
    HolomorphicAt f x ↔ AnalyticAt ℂ f x := by
  sorry
