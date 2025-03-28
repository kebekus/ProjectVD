/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Metric Real

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-!
# The Counting Function of a Meromorphic Function

For nontrivially normed fields `𝕜`, this file defines the logarithmic counting
function of a meromorphic function defined on `𝕜`, as used in Value
Distribution Theory.
-/

/-!
## Definition of the Counting Function
-/

/-- The logarithmic counting function of a function with locally finite support `⊤`. -/
noncomputable def Function.locallyFinsuppWithin.logCounting
    (D : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) :
    ℝ → ℝ :=
  fun r ↦ ∑ᶠ z, D.restrict (by tauto : closedBall (0 : 𝕜) |r| ⊆ ⊤) z * (log r - log ‖z‖)

/-- The logarithmic counting function of a meromorphic function. -/
noncomputable def MeromorphicOn.logCounting (f : 𝕜 → E) (a : WithTop E) :
    ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact (MeromorphicOn.divisor (fun z ↦ f z - a.untop₀) ⊤)⁺.logCounting
  · exact (MeromorphicOn.divisor f ⊤)⁻.logCounting
