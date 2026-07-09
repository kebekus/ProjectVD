/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# Truncated Divisors and Truncated Counting Functions — SMT work package A

See `VD/SMT/PLAN-SecondMainTheorem.md`, §3.

Mathlib target: extend `Mathlib/Topology/LocallyFinsupp.lean` (the truncation operator)
plus new file `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean`
(the counting layer).
Dependencies: none (independently PR-able).

Planned contents:

- `Function.locallyFinsuppWithin.trunc`: truncation of an integer-valued function with
  locally finite support at multiplicity one, `z ↦ min (D z) 1`. This cannot be a lattice
  operation within `locallyFinsuppWithin U ℤ` because the constant function `1` does not
  have locally finite support; the definition imitates the existing `Min` instance,
  reusing `D`'s local-finiteness witnesses. API: `trunc_apply`, `trunc_le`,
  `trunc_nonneg`, `trunc_mono`, `trunc_trunc`, `support_trunc`, `logCounting_trunc_le`,
  `logCounting_trunc_nonneg`.

- `ValueDistribution.truncatedLogCounting`: the truncated logarithmic counting function
  `N̄(r, a)` of value distribution theory — like `logCounting f a`, but counting each
  zero/pole once, regardless of multiplicity. API mirrors `logCounting`:
  `truncatedLogCounting_top/_coe/_zero/_inv/_le/_nonneg/_monotoneOn/_congr_codiscrete`.

The truncated counting function is the quantity through which the Second Main Theorem
(`VD/SMT/SecondMainTheorem.lean`) is classically stated.
-/
