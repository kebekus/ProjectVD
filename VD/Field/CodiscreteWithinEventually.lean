/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Topology.DiscreteSubset

/-!
# Eventual Statements along the Filter `codiscreteWithin`

This file relates eventual statements along the filter `Filter.codiscreteWithin U` to eventual
statements along the punctured neighborhoods of points of `U`: a predicate that holds eventually
along every punctured neighborhood of every point of `U` holds eventually along
`codiscreteWithin U`, for arbitrary sets `U`. For open `U`, the converse holds as well.
-/

open Filter Set Topology

variable {X Y : Type*} [TopologicalSpace X] {U : Set X} {p : X → Prop} {f g : X → Y}

/--
A predicate holds eventually along `codiscreteWithin U` if it holds eventually along the
punctured neighborhood of every point of `U`.
-/
theorem Filter.eventually_codiscreteWithin_of_forall_eventually_nhdsNE
    (h : ∀ x ∈ U, ∀ᶠ y in 𝓝[≠] x, p y) : ∀ᶠ y in codiscreteWithin U, p y :=
  mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun x hx ↦
    mem_of_superset (h x hx) subset_union_left

/--
Two functions agree along `codiscreteWithin U` if they agree along the punctured neighborhood
of every point of `U`.
-/
theorem Filter.eventuallyEq_codiscreteWithin_of_forall_eventuallyEq_nhdsNE
    (h : ∀ x ∈ U, f =ᶠ[𝓝[≠] x] g) : f =ᶠ[codiscreteWithin U] g :=
  eventually_codiscreteWithin_of_forall_eventually_nhdsNE h

/--
On an open set `U`, a predicate holds eventually along `codiscreteWithin U` if and only if it
holds eventually along the punctured neighborhood of every point of `U`.
-/
theorem Filter.eventually_codiscreteWithin_iff_forall_eventually_nhdsNE (hU : IsOpen U) :
    (∀ᶠ y in codiscreteWithin U, p y) ↔ ∀ x ∈ U, ∀ᶠ y in 𝓝[≠] x, p y := by
  refine ⟨fun h x hx ↦ ?_, eventually_codiscreteWithin_of_forall_eventually_nhdsNE⟩
  have := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x hx
  filter_upwards [this, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)] with z hz h₂z
  exact hz.resolve_right fun h₃z ↦ h₃z h₂z

/--
On an open set `U`, two functions agree along `codiscreteWithin U` if and only if they agree
along the punctured neighborhood of every point of `U`. Local version of
`eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE`.
-/
lemma eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE (hU : IsOpen U) :
    f =ᶠ[codiscreteWithin U] g ↔ ∀ x ∈ U, f =ᶠ[𝓝[≠] x] g :=
  Filter.eventually_codiscreteWithin_iff_forall_eventually_nhdsNE hU
