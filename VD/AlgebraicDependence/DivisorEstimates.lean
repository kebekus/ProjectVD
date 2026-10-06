/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Divisor Estimates for Polynomial Relations — Algebraic Dependence work package B

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §4.

Mathlib targets: `Mathlib/Analysis/Meromorphic/Order.lean` (B1),
`Mathlib/Analysis/Meromorphic/Divisor.lean` (B2, B3). Dependencies: none within the project.

Planned results:

- B1, `le_meromorphicOrderAt_sum`: the order of a finite sum is at least the minimum of the
  orders of the summands (Finset induction over `meromorphicOrderAt_add`).
- B2, `MeromorphicOn.nsmul_negPart_divisor_le_of_monic_eq`: the **pole divisor under a monic
  relation**, `d • (div f)⁻ ≤ (div (f ^ d + Σ_{j<d} a j * f ^ j))⁻ + d • Σ_{j<d} (div (a j))⁻`.
  Pointwise `WithTop ℤ` case analysis: either the relation has a pole of order `≥ d k` at a
  pole of order `k` of `f`, or some coefficient has a pole of order `≥ k` there.
- B3 (for package G): the pole divisor of a quotient `P(f) / Q(f)` with a Bezout certificate,
  `(p − q) • (div f)⁻ + (div Q(f))⁺ ≤ (div (P(f)/Q(f)))⁻ + (small divisors)`.
-/
