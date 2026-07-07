/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# Differentiated Poisson Representation — LLD work packages B4–B5

**Status: stub, no content yet.** See `VD/LLD/PLAN-LogarithmicDerivative.md`, §4.

Mathlib target: extend `Mathlib/Analysis/Complex/Poisson.lean` (B4) and
`Mathlib/Analysis/Complex/CanonicalDecomposition.lean` (B5).
Dependencies: `CauchyIntegralDeriv.lean` and the Poisson–Jensen chain
(`VD/MathlibSubmitted/BlaschkeDecomp2.lean`, `VD/MathlibPending/PoissonJensen.lean`).

Planned declarations:

- `logDeriv_eq_circleAverage` (B4) — if `h` is meromorphic on `closedBall 0 R`,
  analytic and nonvanishing on the **open** ball, then for `w ∈ ball 0 R`:
  `logDeriv h w = circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • Real.log ‖h ζ‖) 0 R`.
  Proof: kernel integral is analytic with computable derivative (B1–B3); its real part
  is `log ‖h ·‖` by Poisson–Jensen; `logDeriv h` has a primitive `G` on the ball
  (`DifferentiableOn.isExactOn_ball`), so `h = κ · exp G`; conclude with
  `AnalyticOnNhd.eq_const_of_re_eq_const` and differentiate.
  Nonvanishing is required only on the *open* ball, so the lemma also applies to
  `h = (· - u)` with `u` on the sphere — this yields the boundary-divisor correction
  `circleAverage (fun ζ ↦ (2ζ/(ζ-w)²) • log ‖ζ - u‖) 0 R = (w - u)⁻¹` for free.
- `Complex.logDeriv_canonicalFactor` (B5) —
  `logDeriv (canonicalFactor R a) w = -((w - a)⁻¹ + conj a / (R ^ 2 - conj a * w))`
  away from the two singularities.
- `Complex.norm_logDeriv_canonicalFactor_le` (B5) — for `‖a‖ < ρ`, `‖w‖ = r < ρ`:
  `‖logDeriv (canonicalFactor ρ a) w‖ ≤ ‖w - a‖⁻¹ + (ρ - r)⁻¹`.
-/
