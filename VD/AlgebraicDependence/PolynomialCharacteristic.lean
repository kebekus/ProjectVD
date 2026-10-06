/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
public import VD.AlgebraicDependence.MonicRelation

/-!
# Valiron–Mohon'ko for Polynomials — Algebraic Dependence work package D

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §6.

Mathlib target: `Mathlib/Analysis/Complex/ValueDistribution/AlgebraicDependence.lean` (part 2)
or a sibling `ValironMohonko.lean`. Dependencies: package C and the First Main Theorem
(inversion, `characteristic_sub_characteristic_inv_le`).

Planned results (namespace `ValueDistribution`):

- D1, `characteristic_polynomial_le`: the upper bound
  `T(r, Σ_{j≤d} a j * f ^ j) ≤ d · T(r, f) + Σ_{j≤d} T(r, a j) + log (d + 1)` for `1 ≤ r`.
- D2 = T3, `exists_abs_characteristic_polynomial_sub_le`: the **polynomial Valiron–Mohon'ko
  identity**, two-sided with explicit constants, for `a d` not codiscretely zero.
- D3, `exists_abs_characteristic_polynomial_sub_mem`: the growth-class form, in particular
  Laine's Theorem 2.2.5 for polynomials: `T(r, P(f)) = deg P · T(r, f) + S(r, f)`.
-/
