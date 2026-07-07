/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# Additions to the `posLog` API — LLD work package A (part 2)

**Status: stub, no content yet.** See `VD/LLD/PLAN-LogarithmicDerivative.md`, §3.

Mathlib target: extend `Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean`.
Dependencies: none (independently PR-able).

Planned declarations:

- `Real.posLog_rpow (hx : 0 ≤ x) (hα : 0 ≤ α) : log⁺ (x ^ α) = α * log⁺ x`
  — needed for the exponent-1/2 trick in the two-radius estimate.
- `Real.abs_log_eq_posLog_add_posLog_inv : |log x| = log⁺ x + log⁺ x⁻¹`
  — derived from `half_mul_log_add_log_abs` and `posLog_sub_posLog_inv`;
  used to bound `circleAverage |log ‖f ·‖|` by `m(ρ, f) + m(ρ, f⁻¹)`.
-/
