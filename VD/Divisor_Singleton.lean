/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

import Mathlib.Analysis.Meromorphic.Divisor.Basic
import Mathlib.Tactic.TautoSet

open Classical Filter Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {U : Set 𝕜}

noncomputable def DivisorOn.singleton (x : 𝕜) (hx : x ∈ U) :
    DivisorOn U where
  toFun := fun z ↦ if x = z then 1 else 0
  supportWithinDomain' := by
    intro z hz
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      Decidable.not_not] at hz
    rwa [← hz]
  supportDiscreteWithinDomain' := by
    apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
    intro z hz
    use ⊤, univ_mem' fun a ↦ trivial
    simp only [Set.top_eq_univ, Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false,
      Set.univ_inter]
    have : {b | ¬x = b} = {x}ᶜ := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
      tauto
    by_cases hx : x ∈ U <;> simp_all [hx]

theorem finsupp_singleton (D : DivisorOn U) (hD : Set.Finite D.support) :
    D = ∑ᶠ u : U, (D u.1) • singleton u.1 u.2 := by
  ext x
  rw [finsum_eq_sum]
  sorry
