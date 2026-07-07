/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Additions to the `posLog` API — LLD work package A (part 2)

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §3.

Mathlib target: extend `Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean`.
Dependencies: none (independently PR-able).

This file provides two elementary lemmas on the positive part of the logarithm.

- `Real.posLog_rpow`: `log⁺` commutes with real powers with nonnegative base and
  exponent. This is needed for the exponent-1/2 trick in the two-radius estimate
  of the Lemma on the Logarithmic Derivative.

- `Real.abs_log_eq_posLog_add_posLog_inv`: presentation of `|log|` in terms of
  `log⁺`, used to bound circle averages of `|log ‖f ·‖|` by proximity functions.
-/

namespace Real

variable {x α : ℝ}

/-- The function `log⁺` commutes with real powers with nonnegative base and exponent. -/
theorem posLog_rpow (hx : 0 ≤ x) (hα : 0 ≤ α) : log⁺ (x ^ α) = α * log⁺ x := by
  rcases hx.eq_or_lt with rfl | h₁x
  · rcases eq_or_ne α 0 with rfl | h₁α
    · simp
    · simp [zero_rpow h₁α]
  · rw [posLog_apply, posLog_apply, log_rpow h₁x, mul_max_of_nonneg _ _ hα, mul_zero]

/-- Presentation of `|log|` in terms of the positive part of the logarithm. -/
theorem abs_log_eq_posLog_add_posLog_inv (x : ℝ) : |log x| = log⁺ x + log⁺ x⁻¹ := by
  have h₁ := half_mul_log_add_log_abs (x := x)
  have h₂ := half_mul_log_add_log_abs (x := x⁻¹)
  rw [log_inv, abs_neg] at h₂
  linarith

end Real
