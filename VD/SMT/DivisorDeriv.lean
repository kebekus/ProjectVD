/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# The Divisor of the Derivative — SMT work package B

See `VD/SMT/PLAN-SecondMainTheorem.md`, §4.

Mathlib target: new file `Mathlib/Analysis/Meromorphic/DivisorDeriv.lean`.
Dependencies: `VD/SMT/TruncatedCounting.lean` (package A).

This is the material explicitly reserved for the Second Main Theorem by the docstring of
`VD/LLD/MeromorphicLogDeriv.lean`. Planned contents:

- Order-level lemmas: `meromorphicOrderAt_deriv_eq_top` (infinite order propagates to the
  derivative) and `meromorphicOrderAt_deriv_nonneg` (nonnegative order propagates to the
  derivative), complementing Mathlib's pointwise `meromorphicOrderAt_deriv_eq_sub_one`.

- `MeromorphicOn.negPart_divisor_deriv`: **pole divisor of the derivative** — the poles
  of `deriv f` are exactly the poles of `f`, with multiplicity increased by exactly one:
  `(divisor (deriv f) U)⁻ = (divisor f U)⁻ + ((divisor f U)⁻).trunc`.

- `meromorphicOrderAt_sub_const_eq_zero_of_ne`: at most one target value is attained at
  any point (disjointness of the zero divisors of `f - a` for distinct `a`).

- `MeromorphicOn.posPart_divisor_sub_trunc_le_divisor_deriv` and its several-targets sum
  version: **zero divisor of the derivative** — an `a`-point of `f` of multiplicity `m`
  is a zero of `deriv f` of multiplicity `m - 1`.

- Counting-function corollaries: `N(r, f′) = N(r, f) + N̄(r, f)` (exact equality,
  `logCounting_deriv_top`) and `Σₐ (N(r, a) − N̄(r, a)) ≤ N(r, 1/f′)`
  (`sum_logCounting_sub_truncatedLogCounting_le`). These two inequalities convert the
  ramification term of the Second Main Theorem into truncated counting functions.
-/
