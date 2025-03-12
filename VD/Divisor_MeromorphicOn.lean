/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

import Mathlib.Topology.DiscreteSubset
import VD.ToMathlib.Divisor_MeromorphicOn

open Classical Filter Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {U : Set 𝕜}
  {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace MeromorphicOn

-- TODO: Do that also for analytic functions

theorem congr_codiscreteWithin {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂) (h₂ : Set.EqOn f₁ f₂ Uᶜ) :
    MeromorphicOn f₂ U := by
  intro x hx
  apply (hf₁ x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  filter_upwards [h₁ x hx] with a ha
  simp at ha
  tauto

-- TODO: Do that also for analytic functions

theorem congr_codiscreteWithin_open {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂) (h₂ : IsOpen U) :
    MeromorphicOn f₂ U := by
  intro x hx
  apply (hf₁ x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  have : U ∈ 𝓝[≠] x := by
    apply mem_nhdsWithin.mpr
    use U, h₂, hx, Set.inter_subset_left
  filter_upwards [this, h₁ x hx] with a h₁a h₂a
  simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_setOf_eq, not_and, Decidable.not_not] at h₂a
  tauto

theorem divisorOn_congr_codiscreteWithin [CompleteSpace E] {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (h₁ : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) (h₂ : Set.EqOn f₁ f₂ Uᶜ) :
    divisor f₁ hf₁ = divisor f₂ (hf₁.congr_codiscreteWithin h₁ h₂) := by
  ext x
  by_cases hx : x ∈ U <;> simp [hx]
  · congr 1
    apply (hf₁ x hx).order_congr
    simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
      disjoint_principal_right] at h₁
    filter_upwards [h₁ x hx] with a ha
    simp at ha
    tauto

theorem divisorOn_congr_codiscreteWithin_open [CompleteSpace E] {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicOn f₁ U) (h₁ : f₁ =ᶠ[Filter.codiscreteWithin U] f₂)
    (h₂ : IsOpen U) :
    divisor f₁ hf₁ = divisor f₂ (hf₁.congr_codiscreteWithin_open h₁ h₂) := by
  ext x
  by_cases hx : x ∈ U <;> simp [hx]
  · congr 1
    apply (hf₁ x hx).order_congr
    simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
      disjoint_principal_right] at h₁
    have : U ∈ 𝓝[≠] x := by
      apply mem_nhdsWithin.mpr
      use U, h₂, hx, Set.inter_subset_left
    filter_upwards [this, h₁ x hx] with a h₁a h₂a
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_setOf_eq, not_and, Decidable.not_not] at h₂a
    tauto
