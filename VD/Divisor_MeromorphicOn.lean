/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.Divisor.Basic
import VD.stronglyMeromorphicOn
import VD.ToMathlib.meromorphicOn_levelSetOfOrder
import VD.ToBase

open Classical

/-!
# Divisor of a meromorphic function

This file defines the divisor of a meromorphic function and proves the most basic lemmas about those divisors.

## TODO

- Remove the assumption `CompleteSpace E`.
- Behavior under restriction
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {U : Set 𝕜}
  {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

namespace MeromorphicOn



noncomputable def divisor {f : 𝕜 → E} (hf : MeromorphicOn f U) :
    DivisorOn U where
  toFun := fun z ↦ if hz : z ∈ U then ((hf z hz).order.toBase) else 0
  supportWithinDomain' := by
    intro z hz
    simp at hz
    by_contra h₂z
    simp [h₂z] at hz
  supportDiscreteWithinDomain' := by
    filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
      hf.codiscrete_setOf_order_eq_zero_or_top]
    intro _ _
    simp_all only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_right,
      exists_eq_right, Pi.zero_apply, dite_eq_right_iff, WithTop.toBase_eq_zero_iff]
    tauto

theorem divisor_def {f : 𝕜 → E} (hf : MeromorphicOn f U) :
  hf.divisor z = if hz : z ∈ U then ((hf z hz).order.untopD 0 : ℤ) else 0 := by
  rfl

/-- Simplifier lemma: A divisor evaluates to zero outside its support. -/
@[simp]
lemma eval_outside_support (D : DivisorOn U) (hz : z ∉ U) :
    D z = 0 := Function.nmem_support.mp fun a ↦ hz (D.supportWithinDomain a)

@[simp]
theorem divisor_def' {f : 𝕜 → E} (hf : MeromorphicOn f U) (hz : z ∈ U) :
  hf.divisor z = ((hf z hz).order.untopD 0 : ℤ) := by
  simp_all [hf.divisor_def]

theorem divisor_def₂
  {f : 𝕜 → E}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (hz : z ∈ U)
  (h₂f : (hf z hz).order ≠ ⊤) :
  hf.divisor z = (hf z hz).order.untop h₂f := by
  simp_all [hf.divisor_def]
  refine (WithTop.eq_untop_iff h₂f).mpr ?_
  exact untop'_of_ne_top h₂f

theorem divisor_congr_codiscreteWithin {f₁ f₂ : 𝕜 → E} (h₁f₁ : MeromorphicOn f₁ U)
  (h₁f₂ : MeromorphicOn f₂ U) (hf₁₂ : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
  h₁f₁.divisor = h₁f₂.divisor := by
  sorry

theorem divisor_mul₀ [CompleteSpace 𝕜]
  {f₁ f₂ : 𝕜 → 𝕜}
  {z : 𝕜}
  (hz : z ∈ U)
  (h₁f₁ : MeromorphicOn f₁ U)
  (h₂f₁ : (h₁f₁ z hz).order ≠ ⊤)
  (h₁f₂ : MeromorphicOn f₂ U)
  (h₂f₂ : (h₁f₂ z hz).order ≠ ⊤) :
  (h₁f₁.mul h₁f₂).divisor z = h₁f₁.divisor z + h₁f₂.divisor z := by
  rw [MeromorphicOn.divisor_def₂ h₁f₁ hz h₂f₁]
  rw [MeromorphicOn.divisor_def₂ h₁f₂ hz h₂f₂]
  have B : ((h₁f₁.mul h₁f₂) z hz).order ≠ ⊤ := by
    rw [MeromorphicAt.order_mul (h₁f₁ z hz) (h₁f₂ z hz)]
    simp only [ne_eq, LinearOrderedAddCommGroupWithTop.add_eq_top, not_or]
    tauto
  rw [MeromorphicOn.divisor_def₂ (h₁f₁.mul h₁f₂) hz B]
  simp_rw [MeromorphicAt.order_mul (h₁f₁ z hz) (h₁f₂ z hz)]
  rw [untop_add]

theorem divisor_mul [CompleteSpace 𝕜]
  {f₁ f₂ : 𝕜 → 𝕜}
  (h₁f₁ : MeromorphicOn f₁ U)
  (h₂f₁ : ∀ z, (hz : z ∈ U) → (h₁f₁ z hz).order ≠ ⊤)
  (h₁f₂ : MeromorphicOn f₂ U)
  (h₂f₂ : ∀ z, (hz : z ∈ U) → (h₁f₂ z hz).order ≠ ⊤) :
  (h₁f₁.mul h₁f₂).divisor = h₁f₁.divisor + h₁f₂.divisor := by
  ext z
  by_cases hz : z ∈ U
  · simp only [DivisorOn.coe_add, Pi.add_apply]
    rw [MeromorphicOn.divisor_mul₀ hz h₁f₁ (h₂f₁ z hz) h₁f₂ (h₂f₂ z hz)]
  · simp [hz]

theorem divisor_inv [CompleteSpace 𝕜]
  {f: 𝕜 → 𝕜}
  (h₁f : MeromorphicOn f U) :
  h₁f.inv.divisor = -h₁f.divisor := by
  ext z
  by_cases hz : z ∈ U
  · simp [hz]
    rw [MeromorphicAt.order_inv]
    simp
    by_cases h₂f : (h₁f z hz).order = ⊤
    · simp [h₂f]
    · let A := untop'_of_ne_top (d := 0) h₂f
      rw [← A]
      exact rfl
  · simp [hz]

end MeromorphicOn
