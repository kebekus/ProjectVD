/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# Meromorphic API for the Logarithmic Derivative — LLD work package A

**Status: stub, no content yet.** See `VD/LLD/PLAN-LogarithmicDerivative.md`, §3.

Mathlib target: new file `Mathlib/Analysis/Meromorphic/LogDeriv.lean`.
Dependencies: none (independently PR-able).

Planned declarations:

- `MeromorphicAt.logDeriv` — pointwise meromorphy of `logDeriv f = deriv f / f`
  (one-liner: `h.deriv.div h`).
- `meromorphicOrderAt_logDeriv_eq_neg_one` — at points where
  `meromorphicOrderAt f x ∉ {0, ⊤}`, the logarithmic derivative has a **simple** pole:
  `meromorphicOrderAt (logDeriv f) x = -1`. Proof via `meromorphicOrderAt_div` and
  `meromorphicOrderAt_deriv_eq_sub_one`.
- `meromorphicOrderAt_logDeriv_nonneg` — at order-zero points,
  `0 ≤ meromorphicOrderAt (logDeriv f) x`.
- `logDeriv_congr_codiscreteWithin` — `logDeriv` only depends on the codiscrete class
  (equality on an open codiscrete set gives equality of derivatives there).
- `logDeriv_mul_eventuallyEq` — for meromorphic `f`, `g` with orders `≠ ⊤`:
  `logDeriv (f * g) =ᶠ[codiscrete ℂ] logDeriv f + logDeriv g`;
  plus `finprod` and `zpow` versions, localized to `codiscreteWithin U` as needed
  for the differentiated Poisson–Jensen formula (`PoissonJensenDeriv.lean`).

Out of scope here (kept for the Second Main Theorem): `divisor (logDeriv f)`
computations and `N(r, f′/f)`-type bounds.
-/
