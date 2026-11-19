/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Growth Classes, Bundled — Design Variant of `GrowthClass.lean`

This file is a design study. It has the same mathematical content as
`VD/AlgebraicDependence/GrowthClass.lean`, but bundles the class of functions with the proofs
of its closure properties, following Mathlib's pattern for subobjects: where `GrowthClass.lean`
has the predicate `IsGrowthClass l G` on `G : (ℝ → ℝ) → Prop`, this file has the type
`GrowthClass l` with a `SetLike` instance. The axioms are unchanged.

A **growth class** along a filter `l ≤ atTop` is a class of real functions closed under the
operations that the Nevanlinna characteristic produces: constants, sums, and eventual
domination of eventually nonnegative functions. The two standard instances are the big-O class
`GrowthClass.bigO` for a comparison function `φ` dominating the constants, and the little-o
class `GrowthClass.littleO` for `φ → ∞`. The classical class `S(r, f)` of "small functions"
with respect to a nonconstant meromorphic `f` is the little-o class with `φ = T(r, f)` along
`volume.cofinite ⊓ atTop`.

## Main definitions and results

- `GrowthClass l`: the type of growth classes along `l`, with membership `u ∈ G`.
- `GrowthClass.const_mem`, `GrowthClass.mem_of_le`: the axioms, in terms of membership.
- `GrowthClass.bigO`, `GrowthClass.littleO`: the two instances, with the membership lemmas
  `GrowthClass.mem_bigO` and `GrowthClass.mem_littleO`.

## Differences to `GrowthClass.lean`

- Closure under sums is the instance `AddSubmonoidClass (GrowthClass l) (ℝ → ℝ)`. The lemmas
  `add_mem`, `zero_mem`, `nsmul_mem` and `sum_mem` are therefore Mathlib's generic ones, and
  `IsGrowthClass.zero`, `IsGrowthClass.nsmul` and `IsGrowthClass.sum` have no counterpart here.
- Growth classes along `l` are ordered by inclusion.
- Membership in the two instances does not unfold by `beta`-reduction. It unfolds by `Iff.rfl`,
  through the simp lemmas `GrowthClass.mem_bigO` and `GrowthClass.mem_littleO`.
-/

@[expose] public section

open Asymptotics Filter

/-- A **growth class** along a filter `l ≤ atTop`: a class of real functions closed under
constants, sums, and eventual domination of eventually nonnegative functions. -/
structure GrowthClass (l : Filter ℝ) where
  /-- The functions that belong to the class. -/
  carrier : Set (ℝ → ℝ)
  /-- Growth classes live along filters finer than `atTop`, so that `1 ≤ r` eventually. -/
  le_atTop : l ≤ atTop
  /-- Constants belong to the class. -/
  const_mem' : ∀ c : ℝ, (fun _ ↦ c) ∈ carrier
  /-- The class is closed under sums. -/
  add_mem' : ∀ {u v : ℝ → ℝ}, u ∈ carrier → v ∈ carrier → u + v ∈ carrier
  /-- An eventually nonnegative function eventually dominated by a member of the class belongs
  to the class. -/
  mem_of_le' : ∀ {u v : ℝ → ℝ}, v ∈ carrier → (∀ᶠ r in l, 0 ≤ u r) → (∀ᶠ r in l, u r ≤ v r) →
    u ∈ carrier

namespace GrowthClass

variable {l : Filter ℝ} {u v : ℝ → ℝ}

/-- Eventual domination of nonnegative functions, in the language of `IsBigO`: an eventually
nonnegative `u` with `u ≤ v` eventually satisfies `u =O[l] v`. This is a copy of
`Asymptotics.isBigO_of_eventually_nonneg_of_le` from `GrowthClass.lean`, placed in the namespace
`GrowthClass` so that the two design variants can be imported side by side. -/
theorem isBigO_of_eventually_nonneg_of_le (hu : ∀ᶠ r in l, 0 ≤ u r)
    (huv : ∀ᶠ r in l, u r ≤ v r) : u =O[l] v := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hu, huv] with r hu huv
  rw [one_mul, Real.norm_of_nonneg hu]
  exact huv.trans (le_abs_self _)

instance : SetLike (GrowthClass l) (ℝ → ℝ) :=
  ⟨GrowthClass.carrier, fun G H h ↦ by cases G; cases H; congr!⟩

instance : PartialOrder (GrowthClass l) := .ofSetLike (GrowthClass l)

/-- Growth classes are closed under sums and contain zero. This instance provides `add_mem`,
`zero_mem`, `nsmul_mem` and `sum_mem`. -/
instance : AddSubmonoidClass (GrowthClass l) (ℝ → ℝ) where
  add_mem {G} := G.add_mem'
  zero_mem G := G.const_mem' 0

@[simp]
theorem mem_carrier {G : GrowthClass l} : u ∈ G.carrier ↔ u ∈ G := Iff.rfl

@[ext]
theorem ext {G H : GrowthClass l} (h : ∀ u, u ∈ G ↔ u ∈ H) : G = H := SetLike.ext h

/-- Constants belong to every growth class. -/
theorem const_mem (G : GrowthClass l) (c : ℝ) : (fun _ ↦ c) ∈ G := G.const_mem' c

/-- An eventually nonnegative function eventually dominated by a member of a growth class
belongs to the class. -/
theorem mem_of_le (G : GrowthClass l) (hv : v ∈ G) (hu : ∀ᶠ r in l, 0 ≤ u r)
    (huv : ∀ᶠ r in l, u r ≤ v r) : u ∈ G := G.mem_of_le' hv hu huv

/-- The big-O class along `l` with respect to a comparison function dominating the constants,
as a growth class. -/
def bigO (hl : l ≤ atTop) {φ : ℝ → ℝ} (hφ : (1 : ℝ → ℝ) =O[l] φ) : GrowthClass l where
  carrier := {u | u =O[l] φ}
  le_atTop := hl
  const_mem' c := (isBigO_const_const c one_ne_zero l).trans hφ
  add_mem' hu hv := IsBigO.add hu hv
  mem_of_le' hv hu huv := (isBigO_of_eventually_nonneg_of_le hu huv).trans hv

@[simp]
theorem mem_bigO {hl : l ≤ atTop} {φ : ℝ → ℝ} {hφ : (1 : ℝ → ℝ) =O[l] φ} :
    u ∈ bigO hl hφ ↔ u =O[l] φ := Iff.rfl

/-- The little-o class along `l` with respect to a comparison function tending to infinity, as
a growth class. -/
def littleO (hl : l ≤ atTop) {φ : ℝ → ℝ} (hφ : Tendsto φ l atTop) : GrowthClass l where
  carrier := {u | u =o[l] φ}
  le_atTop := hl
  const_mem' c := by
    refine isLittleO_const_left.2 (Or.inr ?_)
    simpa [Function.comp_def, Real.norm_eq_abs] using tendsto_abs_atTop_atTop.comp hφ
  add_mem' hu hv := IsLittleO.add hu hv
  mem_of_le' hv hu huv := (isBigO_of_eventually_nonneg_of_le hu huv).trans_isLittleO hv

@[simp]
theorem mem_littleO {hl : l ≤ atTop} {φ : ℝ → ℝ} {hφ : Tendsto φ l atTop} :
    u ∈ littleO hl hφ ↔ u =o[l] φ := Iff.rfl

end GrowthClass
