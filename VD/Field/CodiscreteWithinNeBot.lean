/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Perfect

/-!
# Nontriviality of the Filter `codiscreteWithin`

This file provides criteria guaranteeing that the filter `Filter.codiscreteWithin S` is not the
bottom filter: this happens iff `S` is not discrete, and in particular whenever `S` has an
accumulation point in itself, whenever `S` is preperfect and nonempty, or whenever `S` is
preconnected with more than one point.

Nontriviality of `codiscreteWithin S` guarantees that the germ ring
`Filter.Germ (codiscreteWithin S) 𝕜` is nontrivial.
-/

open Filter Set Topology

variable {X : Type*} [TopologicalSpace X] {S : Set X} {x : X}

/-- The filter `codiscreteWithin S` is nontrivial iff `S` is not discrete. -/
theorem Filter.codiscreteWithin_neBot_iff : (codiscreteWithin S).NeBot ↔ ¬IsDiscrete S := by
  rw [neBot_iff, not_iff_not, codiscreteWithin_eq_bot_iff]

/-- The filter `codiscreteWithin S` is nontrivial if some point of `S` is an accumulation point
of `S`. -/
theorem AccPt.codiscreteWithin_neBot (hx : x ∈ S) (h : AccPt x (𝓟 S)) :
    (codiscreteWithin S).NeBot := by
  have := accPt_principal_iff_nhdsWithin.1 h
  exact neBot_of_le (le_iSup₂ (f := fun x _ ↦ 𝓝[S \ {x}] x) x hx)

/-- The filter `codiscreteWithin S` is nontrivial if `S` is preperfect and nonempty. -/
theorem Preperfect.codiscreteWithin_neBot (hS : Preperfect S) (hne : S.Nonempty) :
    (codiscreteWithin S).NeBot := by
  obtain ⟨x, hx⟩ := hne
  exact (hS x hx).codiscreteWithin_neBot hx

/-- The filter `codiscreteWithin S` is nontrivial if `S` is preconnected and has at least two
points. -/
theorem IsPreconnected.codiscreteWithin_neBot [T1Space X] (hS : IsPreconnected S)
    (h2S : S.Nontrivial) : (codiscreteWithin S).NeBot :=
  (hS.preperfect_of_nontrivial h2S).codiscreteWithin_neBot h2S.nonempty
