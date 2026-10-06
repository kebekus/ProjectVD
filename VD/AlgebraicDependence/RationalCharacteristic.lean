/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Coprime.Basic
public import VD.AlgebraicDependence.GrowthField

/-!
# Valiron–Mohon'ko for Rational Functions — Algebraic Dependence work package G

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §9.

Mathlib target: follows the germ field `VD/Field/` upstream. Dependencies: package F, the
Bezout estimates of packages A (G2) and B (B3).

Planned results (namespace `MeromorphicOn.GermRing`, `F` a growth field, `P Q : F[X]`,
`a : germRing ℂ univ`):

- G1: the upper bound `T(r, P(a)/Q(a)) ≤ max (deg P) (deg Q) · T(r, a) + S(r)`, by induction
  on `deg Q` along the Euclidean algorithm (no coprimality needed).
- G3: the lower bound for coprime `P, Q`, via a Bezout certificate `U * P + V * Q = 1`
  (`IsCoprime`), the pointwise estimate G2 and the divisor estimate B3.
- T8, `exists_abs_characteristic_aeval_div_sub_le`: the **Valiron–Mohon'ko identity**
  `T(r, R(a)) = deg R · T(r, a) + S(r)` for `R = P/Q` with coefficients in a growth field.
- T9: the classical form with `S(r) = o(T(r, f))` along `volume.cofinite ⊓ atTop`
  (Laine, Theorem 2.2.5).
-/
