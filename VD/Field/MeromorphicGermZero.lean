/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import VD.Field.CodiscreteWithinEventually

/-!
# Vanishing Germs of Meromorphic Functions

This file characterizes meromorphic functions on `U` that vanish along the filter
`codiscreteWithin U`: on a preperfect set, these are exactly the functions of infinite order at
every point of `U`; on a preconnected set with at least two points, infinite order at a single
point suffices. As a complement, a function of finite order everywhere satisfies
`f * f⁻¹ =ᶠ[codiscreteWithin U] 1`.

These are the key ingredients in the construction of the field of meromorphic functions on a
connected set, where they identify the invertible germs.
-/

open Filter Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f : 𝕜 → E} {s : 𝕜 → 𝕜'} {U : Set 𝕜}

/--
A function meromorphic on a preperfect set `U` vanishes along `codiscreteWithin U` iff it has
infinite order at every point of `U`.
-/
theorem MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top
    (hf : MeromorphicOn f U) (hU : Preperfect U) :
    f =ᶠ[codiscreteWithin U] 0 ↔ ∀ x ∈ U, meromorphicOrderAt f x = ⊤ := by
  constructor
  · intro h x hx
    exact meromorphicOrderAt_eq_top_iff.2
      ((hf x hx).eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin hx (hU x hx) h)
  · intro h
    exact eventuallyEq_codiscreteWithin_of_forall_eventuallyEq_nhdsNE fun x hx ↦
      meromorphicOrderAt_eq_top_iff.1 (h x hx)

/--
A function meromorphic on a preconnected set `U` with at least two points vanishes along
`codiscreteWithin U` iff it has infinite order at one point of `U`.
-/
theorem MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_exists_meromorphicOrderAt_eq_top
    (hf : MeromorphicOn f U) (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) :
    f =ᶠ[codiscreteWithin U] 0 ↔ ∃ x ∈ U, meromorphicOrderAt f x = ⊤ := by
  have hU : Preperfect U := h₁U.preperfect_of_nontrivial h₂U
  rw [hf.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top hU]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h₂U.nonempty
    exact ⟨x, hx, h x hx⟩
  · rintro ⟨x, h₁x, h₂x⟩ y hy
    by_contra hcon
    exact (hf.exists_meromorphicOrderAt_ne_top_iff_forall_mem
      ⟨h₂U.nonempty, h₁U⟩).1 ⟨y, hy, hcon⟩ x h₁x h₂x

/--
If a function meromorphic on `U` has finite order at every point of `U`, then `f * f⁻¹` equals
one along `codiscreteWithin U`.
-/
theorem MeromorphicOn.self_mul_inv_eventuallyEq_one_codiscreteWithin (hs : MeromorphicOn s U)
    (h : ∀ x ∈ U, meromorphicOrderAt s x ≠ ⊤) :
    s * s⁻¹ =ᶠ[codiscreteWithin U] 1 :=
  (MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hs h).mono
    fun _ hz ↦ mul_inv_cancel₀ hz
