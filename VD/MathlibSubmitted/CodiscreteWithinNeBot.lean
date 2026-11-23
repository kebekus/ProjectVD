/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Perfect

/-!
# Nontriviality of the Filter `codiscreteWithin`

This file provides criteria guaranteeing that the filter `Filter.codiscreteWithin S` is not the
bottom filter: this happens iff `S` is not discrete, and in particular whenever `S` has an
accumulation point in itself, whenever `S` is preperfect and nonempty, or whenever `S` is
preconnected with more than one point.

Nontriviality of `codiscreteWithin S` guarantees that the germ ring
`Filter.Germ (codiscreteWithin S) 𝕜` is nontrivial.
-/

/-
UPSTREAMING INSTRUCTIONS (delete this comment when copying)

Part of the PR "field of meromorphic functions", together with `VD/Field/GermAlgebra.lean` and
`VD/Field/MeromorphicFunctionField.lean`.

This file does not become a Mathlib file. Its four lemmas go into two existing Mathlib files; the
two blocks below are marked accordingly. The module docstring above is not copied.

The split is forced by the import graph: `Mathlib/Topology/Perfect.lean` sees
`Mathlib/Topology/DiscreteSubset.lean` transitively, but not the other way round. Neither target
file needs a new import.
-/

@[expose] public section

open Filter Set Topology

variable {X : Type*} [TopologicalSpace X]

/-
BLOCK 1 — target: `Mathlib/Topology/DiscreteSubset.lean`

Insert directly after `codiscreteWithin_eq_bot_iff`, inside `section codiscrete_filter` and before
`section T1Space`. The target file has `open Set Filter Function Topology` and
`variable {X Y Z : Type*} [TopologicalSpace X] {s : Set X}`; the binders `{S : Set X}` and
`{x : X}` are not variables there and have to be written out, as done below.
-/

/-- The filter `codiscreteWithin S` is nontrivial iff `S` is not discrete. -/
theorem codiscreteWithin_neBot_iff {S : Set X} : (codiscreteWithin S).NeBot ↔ ¬ IsDiscrete S := by
  rw [neBot_iff, not_iff_not, codiscreteWithin_eq_bot_iff]

/--
The filter `codiscreteWithin S` is nontrivial if some point of `S` is an accumulation point of `S`.
-/
theorem AccPt.codiscreteWithin_neBot {S : Set X} {x : X} (hx : x ∈ S) (h : AccPt x (𝓟 S)) :
    (codiscreteWithin S).NeBot := by
  have := accPt_principal_iff_nhdsWithin.1 h
  exact neBot_of_le (le_iSup₂ (f := fun x _ ↦ 𝓝[S \ {x}] x) x hx)

/-
BLOCK 2 — target: `Mathlib/Topology/Perfect.lean`

Insert directly after `IsPreconnected.preperfect_of_nontrivial`, inside `section Preperfect`. The
target file has `open Filter Set TopologicalSpace`, `open scoped Topology` and
`variable {α : Type*} [TopologicalSpace α] {C : Set α}`: the ambient type is called `α` there, so
rename `X` to `α` in the two statements. Nothing else changes.
-/

/-- The filter `codiscreteWithin S` is nontrivial if `S` is preperfect and nonempty. -/
theorem Preperfect.codiscreteWithin_neBot {S : Set X} (hS : Preperfect S) (hne : S.Nonempty) :
    (codiscreteWithin S).NeBot := by
  obtain ⟨x, hx⟩ := hne
  exact (hS x hx).codiscreteWithin_neBot hx

/--
The filter `codiscreteWithin S` is nontrivial if `S` is preconnected and has at least two points.
-/
theorem IsPreconnected.codiscreteWithin_neBot [T1Space X] {S : Set X} (hS : IsPreconnected S)
    (h2S : S.Nontrivial) : (codiscreteWithin S).NeBot :=
  (hS.preperfect_of_nontrivial h2S).codiscreteWithin_neBot h2S.nonempty
