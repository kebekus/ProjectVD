/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.DiscreteSubset

/-!
# Lemmas about the Codiscrete Filter

This file collects general-purpose lemmas about the filter `Filter.codiscrete` of codiscrete
sets: a characterization in terms of punctured neighborhoods, nonvanishing of polynomials away
from codiscrete sets, and a congruence lemma for derivatives.
-/

open Filter Set Topology

variable {X : Type*} [TopologicalSpace X] {Y : Type*}

/-!
## Codiscrete Sets and Punctured Neighborhoods
-/

/-- A set is codiscrete iff it is a punctured neighborhood of every point. -/
lemma mem_codiscrete_iff_forall_mem_nhdsNE {s : Set X} :
    s ∈ Filter.codiscrete X ↔ ∀ x, s ∈ 𝓝[≠] x := by
  simp [Filter.codiscrete, mem_codiscreteWithin_iff_forall_mem_nhdsNE]

/-- Codiscrete sets are punctured neighborhoods of every point. -/
lemma mem_nhdsNE_of_mem_codiscrete {s : Set X} (hs : s ∈ Filter.codiscrete X) (x : X) :
    s ∈ 𝓝[≠] x :=
  mem_codiscrete_iff_forall_mem_nhdsNE.1 hs x

/--
Two functions agree along the codiscrete filter iff they agree along the punctured
neighborhood of every point.
-/
lemma eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE {f₁ f₂ : X → Y} :
    f₁ =ᶠ[Filter.codiscrete X] f₂ ↔ ∀ x, f₁ =ᶠ[𝓝[≠] x] f₂ := by
  simp [EventuallyEq, Filter.Eventually, mem_codiscrete_iff_forall_mem_nhdsNE]

/-!
## Nonvanishing of Polynomials
-/

/-- Nonzero polynomials are nonzero away from a codiscrete set. -/
lemma eventually_eval_ne_zero_codiscrete {R : Type*} [CommRing R] [IsDomain R]
    [TopologicalSpace R] [T1Space R] {g : Polynomial R} (hg : g ≠ 0) :
    ∀ᶠ z in Filter.codiscrete R, g.eval z ≠ 0 := by
  filter_upwards [(Polynomial.finite_setOfPred_isRoot hg).compl_mem_codiscrete] with z hz
  exact hz

/-!
## Congruence Lemma for Derivatives

Like the logarithmic derivative (`logDeriv_congr_codiscreteWithin`), the derivative on an
open set `U` only depends on the equivalence class of the function with respect to
equality away from codiscrete subsets of `U`. This is pure calculus and requires no
meromorphy assumption.
-/

/--
If two functions agree on a codiscrete subset of an open set `U`, then so do their derivatives.
-/
theorem deriv_congr_codiscreteWithin {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : 𝕜 → E} {U : Set 𝕜}
    (hU : IsOpen U) (h : f =ᶠ[codiscreteWithin U] g) :
    deriv f =ᶠ[codiscreteWithin U] deriv g := by
  filter_upwards [h, self_mem_codiscreteWithin U] with y h₁y h₂y
  apply Filter.EventuallyEq.deriv_eq
  have h₄ : {z | f z = g z} ∪ Uᶜ ∈ 𝓝 y := by
    rw [← nhdsNE_sup_pure y, mem_sup]
    exact ⟨mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h y h₂y,
      mem_pure.2 (mem_union_left _ h₁y)⟩
  filter_upwards [h₄, hU.mem_nhds h₂y] with z h₁z h₂z
  rcases h₁z with h₁z | h₁z
  · exact h₁z
  · exact absurd h₂z h₁z
