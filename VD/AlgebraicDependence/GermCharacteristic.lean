/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
public import VD.AlgebraicDependence.MonicRelation
public import VD.Field.GermFieldAPI

/-!
# The Characteristic of a Meromorphic Germ — Algebraic Dependence work packages F0–F1

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §8.

Mathlib target: follows the germ field `VD/Field/` upstream. Dependencies: `VD/Field/`,
package C (for the hypothesis-free product bound C0).

Planned content:

- F0: `Fact` instances making `MeromorphicOn.germRing ℂ Set.univ` a field and a `ℂ`-algebra
  globally; the coercion `MeromorphicOn.GermRing.toGerm` of a meromorphic function to its germ.
- F1: `MeromorphicOn.GermRing.characteristic : germRing ℂ univ → ℝ → ℝ`, the Nevanlinna
  characteristic of a germ through its chosen representative, with `characteristic_toGerm`
  (independence of the representative for `r ≠ 0`) and the transported arithmetic:
  `characteristic_add_le`, `characteristic_sum_le`, `characteristic_mul_le`,
  `characteristic_pow`, `exists_abs_characteristic_inv_sub_le`, `characteristic_algebraMap`,
  `characteristic_nonneg`.
-/
