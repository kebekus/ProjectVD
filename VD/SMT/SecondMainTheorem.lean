/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# The Second Main Theorem, Truncated Form — SMT work package F

See `VD/SMT/PLAN-SecondMainTheorem.md`, §8.

Mathlib target: `Mathlib/Analysis/Complex/ValueDistribution/SecondMainTheorem.lean`
(part 3 of 3).
Dependencies: `VD/SMT/TruncatedCounting.lean` (package A), `VD/SMT/DivisorDeriv.lean`
(package B), `VD/SMT/SecondMainTheoremRamification.lean` (package E).

Planned contents:

- S2, `ValueDistribution.secondMainTheorem`: **the Second Main Theorem** in its classical
  truncated form — for a meromorphic function `f` on `ℂ` and a finite set
  `S : Finset (WithTop ℂ)` of targets,
  `(#S − 2)·T(r) ≤ Σ_{a ∈ S} N̄(r, a) + c·(log⁺ T(r) + log r)` for all large `r` outside
  a set of finite Lebesgue measure. No hypotheses beyond meromorphy of `f`.

- S2′, `ValueDistribution.secondMainTheorem_posPart`: the posPart reformulation as an
  `IsBigO` statement along `volume.cofinite ⊓ atTop`.

- Helpers flagged for upstreaming into `FirstMainTheorem.lean`:
  `characteristic_coe_eq_characteristic_shift_inv` and the combined First Main Theorem
  `exists_abs_characteristic_coe_sub_characteristic_top_le`
  (`|T(r, a) − T(r, ∞)| ≤ C`).

The proof combines S1 (package E) with the First Main Theorem to convert proximity into
counting functions, then absorbs the multiplicity excess into the ramification term using
the two counting inequalities of package B.
-/
