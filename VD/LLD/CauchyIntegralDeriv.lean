/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# Derivative of the Cauchy Integral — LLD work packages B1–B3

**Status: stub, no content yet.** See `VD/LLD/PLAN-LogarithmicDerivative.md`, §4.

Mathlib target: extend `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`
(and/or `Mathlib/Analysis/Complex/Poisson.lean`).
Dependencies: none (independently PR-able).

Planned declarations:

- `hasDerivAt_circleIntegral_sub_inv_smul` — for `CircleIntegrable g c R` and
  `w ∈ ball c R`, the Cauchy-type integral `fun w ↦ ∮ z in C(c, R), (z - w)⁻¹ • g z`
  has derivative `∮ z in C(c, R), ((z - w) ^ 2)⁻¹ • g z` at `w`.
  Proof via `hasDerivAt_integral_of_dominated_loc_of_deriv_le` over `𝕜 = ℂ`.
  Complements `hasFPowerSeriesOn_cauchy_integral` (which gives analyticity, but not
  this closed form at off-center points).
- `hasDerivAt_circleAverage_herglotzRieszKernel_smul` — the same for the
  Herglotz–Riesz kernel integral `F g w := circleAverage (herglotzRieszKernel 0 w • g) 0 R`,
  using `herglotzRieszKernel 0 w ζ = 2 * ζ * (ζ - w)⁻¹ - 1` and
  `circleAverage_eq_circleIntegral`; the derivative is
  `circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • g ζ) 0 R`.
- `re_circleAverage_herglotzRieszKernel_smul` — for real `g`, the real part of `F g w`
  is `circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 R`
  (real part commutes with the integral).
-/
