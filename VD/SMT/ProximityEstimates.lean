/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# Proximity Estimates for the Second Main Theorem — SMT work package D

See `VD/SMT/PLAN-SecondMainTheorem.md`, §6.

Mathlib target: `Mathlib/Analysis/Complex/ValueDistribution/SecondMainTheorem.lean`
(part 1 of 3).
Dependencies: `VD/SMT/DivisorDeriv.lean` (package B), `VD/SMT/SeparationLemma.lean`
(package C), the Lemma on the Logarithmic Derivative (`VD/LLD/LogDerivLemma.lean`), and
the pending `VD/MathlibPending/CharacteristicMoebius.lean` (D1 only).

Planned contents:

- D1, `Meromorphic.eventuallyEq_const_of_exists_meromorphicOrderAt_deriv_eq_top`: the
  constancy dichotomy — a meromorphic function on `ℂ` whose derivative vanishes somewhere
  to infinite order is constant away from a discrete set. This isolates the degenerate
  case of the hypothesis-free Second Main Theorem.

- D2, `ValueDistribution.isBigO_proximity_logDeriv_shift`: `m(r, f′/(f − a)) = S(r)` —
  the Lemma on the Logarithmic Derivative for `f - a`, with the error expressed through
  the characteristic of `f` itself (via the First Main Theorem, shift invariance).

- D3, `ValueDistribution.proximity_deriv_top_le`: `m(r, f′) ≤ m(r, f) + m(r, f′/f)`.

- D4, `ValueDistribution.sum_proximity_le`: the integrated separation bound
  `Σₐ m(r, a) ≤ m(r, 1/f′) + Σₐ m(r, f′/(f − a)) + c`, obtained by applying the
  separation lemma pointwise on circles and comparing circle averages.
-/
