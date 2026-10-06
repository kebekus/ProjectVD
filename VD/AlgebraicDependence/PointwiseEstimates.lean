/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Pointwise `log⁺` Estimates for Polynomial Relations — Algebraic Dependence work package A

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §3 (and §9, G2).

Mathlib target: `Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean` or a new sibling file.
Dependencies: none beyond `PosLog`. Pure `NormedField` algebra, no meromorphy, no integration.

Planned results (all in `namespace Real`, for `w, g, a j : 𝕜` with `[NormedField 𝕜]`):

- `nsmul_posLog_norm_le_of_monic_eq`: the **weighted root bound**
  `d · log⁺ ‖w‖ ≤ log⁺ ‖g‖ + d · Σ_{j<d} log⁺ ‖a j‖ + d · log (2 (d + 1))` for solutions of
  `w ^ d + Σ_{j<d} a j * w ^ j = g`. The factor `d` in front of `log⁺ ‖w‖` is what the Cauchy
  bound `Polynomial.IsRoot.norm_lt_cauchyBound` cannot give.
- `posLog_norm_le_of_monic_eq_zero`: the unweighted bound with the sharper constant `log d`.
- `posLog_norm_le_of_pow_mul_eq`: Clunie's lemma, pointwise.
- `posLog_norm_inv_le_of_eq_zero`: Mohon'ko's lemma, pointwise (needs `a 0 ≠ 0`).
- `nsmul_posLog_norm_add_posLog_norm_inv_le`: the Bezout estimate for the lower bound of the
  rational Valiron–Mohon'ko identity (package G).
-/
