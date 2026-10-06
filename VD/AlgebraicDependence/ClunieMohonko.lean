/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
public import VD.AlgebraicDependence.PointwiseEstimates
public import VD.LLD.LogDerivEstimates

/-!
# Clunie's Lemma and Mohon'ko's Lemma — Algebraic Dependence work package E

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §7.

Mathlib target: new file `Mathlib/Analysis/Complex/ValueDistribution/Clunie.lean`.
Dependencies: package A and `circleAverage_mono_codiscreteWithin`
(`VD/LLD/LogDerivEstimates.lean`).

Both results are the algebraic (derivative-free) cases of Laine, Chapter 2.4; the differential
versions are a follow-up (plan §10).

Planned results (namespace `ValueDistribution`):

- T4, `proximity_le_of_pow_mul_eq`: **Clunie's lemma**: if
  `f ^ n * P(f) =ᶠ[codiscrete ℂ] Q(f)` with `deg Q ≤ n`, then
  `m(r, P(f)) ≤ Σ m(r, coefficients of P) + Σ m(r, coefficients of Q) + log (max (p+1) (n+1))`.
- T5, `proximity_zero_le_of_eq_zero`: **Mohon'ko's lemma**: if `P(f) =ᶠ[codiscrete ℂ] 0` with
  constant coefficient `a 0` not codiscretely zero, then
  `m(r, 1/f) ≤ m(r, 1/a 0) + Σ_{j≥1} m(r, a j) + log d`.
- Classical corollaries with coefficients in `S(f)`: `m(r, P(f)) = S(r, f)` and
  `m(r, 1/f) = S(r, f)`.
-/
