/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# Deficiency and the Defect Relation — SMT work package G

See `VD/SMT/PLAN-SecondMainTheorem.md`, §9.

Mathlib target: new file `Mathlib/Analysis/Complex/ValueDistribution/Deficiency.lean`.
Dependencies: `VD/SMT/TruncatedCounting.lean` (package A),
`VD/SMT/SecondMainTheorem.lean` (package F); uses the pending
`VD/MathlibPending/BoundednessCharacteristic.lean` for the nonconstancy bridge.

Planned contents:

- `ValueDistribution.deficiency`: the Nevanlinna deficiency
  `δ(a) = liminf_{r → ∞} m(r, a) / T(r)`, and `ValueDistribution.truncatedDeficiency`:
  the truncated deficiency `Θ(a) = 1 − limsup_{r → ∞} N̄(r, a) / T(r)`.

- Basic API under `Tendsto (characteristic f ⊤) atTop atTop`: the deficiencies lie in
  `[0, 1]`, `δ(a) ≤ Θ(a)`, `δ(a) = 1 − limsup N(r, a)/T(r)` (via the First Main Theorem),
  omitted values have deficiency one; the bridge
  `tendsto_characteristic_atTop_of_not_eventuallyConst`.

- S3, `ValueDistribution.sum_truncatedDeficiency_le`: **the defect relation** — for a
  transcendental meromorphic function (`Real.log =o[atTop] characteristic f ⊤`) and any
  finite target set `S : Finset (WithTop ℂ)`, `Σ_{a ∈ S} Θ(a) ≤ 2`; with the corollary
  `sum_deficiency_le` for the classical defects. Small standalone pieces:
  `NeBot (volume.cofinite ⊓ atTop)` and finite subadditivity of `limsup`.

The defect relation for *rational* functions is a separate algebraic fact and deliberately
out of scope (see design decision 8 of the plan).
-/
