/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
public import Mathlib.Analysis.Meromorphic.RCLike
public import VD.AlgebraicDependence.DivisorEstimates
public import VD.AlgebraicDependence.PointwiseEstimates

/-!
# The Master Inequality and Algebraic Dependence — Algebraic Dependence work package C

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §5.

Mathlib target: new file `Mathlib/Analysis/Complex/ValueDistribution/AlgebraicDependence.lean`
(C0 goes to `CharacteristicFunction.lean`). Dependencies: packages A and B.

Planned results (namespace `ValueDistribution`, `f g : ℂ → ℂ`, coefficients `a : ℕ → ℂ → ℂ`):

- C0, `characteristic_mul_top_le'`: `T(r, f₁ f₂) ≤ T(r, f₁) + T(r, f₂)` for `1 ≤ r`, without
  the `meromorphicOrderAt ≠ ⊤` hypotheses of `characteristic_mul_top_le`.
- C1/C2: integration of the pointwise estimate (A) and of the divisor estimate (B2).
- T1, `nsmul_characteristic_le_of_monic_eq`: the **master inequality**
  `d · T(r, f) ≤ T(r, g) + d · Σ_{j<d} T(r, a j) + d · log (2 (d + 1))` whenever
  `f ^ d + Σ_{j<d} a j * f ^ j =ᶠ[codiscrete ℂ] g`.
- T2, `characteristic_le_sum_characteristic_of_monic_eq_zero`: the **algebraic dependence
  bound** `T(r, f) ≤ Σ_{j<d} T(r, a j) + log d` for `g = 0`.
- C5: asymptotic corollaries (`=O`, `=o`): algebraic over small functions ⟹ small.
-/
