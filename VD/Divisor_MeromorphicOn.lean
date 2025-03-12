/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

import Mathlib.Topology.DiscreteSubset
import VD.ToMathlib.Divisor_MeromorphicOn

open Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {U : Set 𝕜}
  {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

namespace MeromorphicOn

theorem congr_codiscrete [CompleteSpace 𝕜] {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (h : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
    MeromorphicOn f₂ U := by
  intro x hx
  apply (hf₁ x hx).congr
  let Z := h.
  --simp_rw [Filter.mem_codiscreteWithin, Filter.disjoint_principal_right] at h
  rw [Filter.eventuallyEq_iff_exists_mem] at h
    use {a}ᶜ
    constructor
    · simp_rw [mem_codiscreteWithin, Filter.disjoint_principal_right]

  rw [Filter.EventuallyEq, mem_codiscreteWithin] at h
  sorry

theorem divisorOn_congr [CompleteSpace 𝕜] {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (h : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
    divisor f₁ hf₁ = divisor f₂ (hf₁.congr_codiscrete h) := by
  sorry
