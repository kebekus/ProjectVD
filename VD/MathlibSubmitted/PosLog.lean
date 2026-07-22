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

This file provides several elementary lemmas on the positive part of the logarithm.

- `Real.posLog_rpow`: `log⁺` commutes with real powers with nonnegative base and
  exponent. This is needed for the exponent-1/2 trick in the two-radius estimate
  of the Lemma on the Logarithmic Derivative.

- `Real.abs_log_eq_posLog_add_posLog_inv`: presentation of `|log|` in terms of
  `log⁺`, used to bound circle averages of `|log ‖f ·‖|` by proximity functions.

- `Real.posLog_le_log_one_add` and `Real.log_one_add_le_posLog`: two-sided comparison
  of `log⁺ x` with `log (1 + x)` for nonnegative `x`, tight up to the additive
  constant `log 2`.

- `Real.posLog_le_abs`: the elementary bound `log⁺ x ≤ |x|`.
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

/-- For nonnegative `x`, the positive part of the logarithm is bounded by `log (1 + x)`. -/
lemma posLog_le_log_one_add {x : ℝ} (hx : 0 ≤ x) : log⁺ x ≤ Real.log (1 + x) := by
  rw [posLog_apply]
  apply max_le (Real.log_nonneg (by linarith))
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  · exact Real.log_le_log hx' (by linarith)

/-- The positive part of the logarithm is bounded by the absolute value: `log⁺ x ≤ |x|`. -/
lemma posLog_le_abs (x : ℝ) : log⁺ x ≤ |x| := by
  rcases le_or_gt |x| 1 with h | h
  · rw [(posLog_eq_zero_iff x).2 h]
    exact abs_nonneg x
  · rw [← posLog_abs, posLog_eq_log (by rw [abs_abs]; exact h.le)]
    linarith [Real.log_le_sub_one_of_pos (lt_trans one_pos h : (0:ℝ) < |x|)]

/-- For nonnegative `x`, the reverse bound `log (1 + x) ≤ log⁺ x + log 2` holds, giving a
converse to `posLog_le_log_one_add` up to the additive constant `log 2`. -/
lemma log_one_add_le_posLog {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ log⁺ x + Real.log 2 := by
  rw [posLog_eq_log_max_one hx]
  have h₁ : (1 : ℝ) + x ≤ max 1 x * 2 := by
    rcases le_total x 1 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith
  calc Real.log (1 + x)
      ≤ Real.log (max 1 x * 2) := Real.log_le_log (by linarith) h₁
    _ = Real.log (max 1 x) + Real.log 2 :=
        Real.log_mul (by positivity) two_ne_zero

end Real
