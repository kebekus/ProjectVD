/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Metric Real

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜}

/-!
## Derived invariants
-/

/-- The degree of a divisor is the sum of its values, or 0 if the support is
infinite. -/
noncomputable def deg (D : Function.locallyFinsupp U ℤ) : ℤ := ∑ᶠ z, D.toFun z

/-- The counting function for a divisor defined on ⊤ -/
noncomputable def counting (D : Function.locallyFinsupp 𝕜 ℤ) : ℝ → ℝ :=
  fun r ↦ ∑ᶠ z, D.restrict (by tauto : closedBall (0 : 𝕜) |r| ⊆ ⊤) z

/-- The logarithmic counting function for a divisor defined on ⊤ -/
noncomputable def logCounting (D : Function.locallyFinsupp 𝕜 ℤ) : ℝ → ℝ :=
  fun r ↦ ∑ᶠ z, D.restrict (by tauto : closedBall (0 : 𝕜) |r| ⊆ ⊤) z * (log r - log ‖z‖)
