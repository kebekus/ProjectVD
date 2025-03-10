/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.Divisor.Basic
import VD.ToMathlib.meromorphicOn_levelSetOfOrder
import VD.ToBase

open Classical

/-!
# Divisor of a meromorphic function

This file defines the divisor of a meromorphic function and proves the most
basic lemmas about those divisors.

## TODO

- Remove the assumption `CompleteSpace E`.
- Behavior under restriction of divisors/functions
- Non-negativity of the divisor for an analytic function
- Behavior under multiplication and addition of functions
- Congruence lemmas for `codiscreteWithin`
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

/-- Definition of the divisor. -/
theorem divisor_def {f : 𝕜 → E} (hf : MeromorphicOn f U) :
    hf.divisor z = if hz : z ∈ U then (hf z hz).order.toBase else 0 := by rfl

/-- Simplifier lemma: A divisor on `U` evaluates to zero outside of `U`. -/
@[simp] lemma eval_outside_domain (D : DivisorOn U) (hz : z ∉ U) :
    D z = 0 := Function.nmem_support.mp fun a ↦ hz (D.supportWithinDomain a)

/-- Simplifier lemma: On `U`, the divisor of a function `f` that is meromorphic
on `U` evaluates to `order.toBase`. -/
@[simp] lemma eval_of_divisor_outside_domain {f : 𝕜 → E} (hf : MeromorphicOn f U) (hz : z ∈ U) :
    hf.divisor z = (hf z hz).order.toBase := by simp_all [hf.divisor_def, hz]

theorem divisor_congr_codiscreteWithin {f₁ f₂ : 𝕜 → E} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (hf₁₂ : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
    h₁f₁.divisor = h₁f₂.divisor := by
  ext z
  sorry

theorem divisor_smul [CompleteSpace 𝕜]
  {f₁ : 𝕜 → 𝕜}
  {f₂ : 𝕜 → E}
  (h₁f₁ : MeromorphicOn f₁ U)
  (h₁f₂ : MeromorphicOn f₂ U)
  (h₂f₁ : ∀ z, (hz : z ∈ U) → (h₁f₁ z hz).order ≠ ⊤)
  (h₂f₂ : ∀ z, (hz : z ∈ U) → (h₁f₂ z hz).order ≠ ⊤) :
  (h₁f₁.smul h₁f₂).divisor = h₁f₁.divisor + h₁f₂.divisor := by
  ext z
  by_cases hz : z ∈ U
  · simp_all [(h₁f₁ z hz).order_smul (h₁f₂ z hz)]
  · simp [hz]

theorem divisor_mul [CompleteSpace 𝕜]
  {f₁ f₂ : 𝕜 → 𝕜}
  (h₁f₁ : MeromorphicOn f₁ U)
  (h₁f₂ : MeromorphicOn f₂ U)
  (h₂f₁ : ∀ z, (hz : z ∈ U) → (h₁f₁ z hz).order ≠ ⊤)
  (h₂f₂ : ∀ z, (hz : z ∈ U) → (h₁f₂ z hz).order ≠ ⊤) :
  (h₁f₁.mul h₁f₂).divisor = h₁f₁.divisor + h₁f₂.divisor := by
  ext z
  by_cases hz : z ∈ U
  · simp_all [(h₁f₁ z hz).order_mul (h₁f₂ z hz)]
  · simp [hz]

theorem divisor_inv [CompleteSpace 𝕜]
  {f: 𝕜 → 𝕜}
  (h₁f : MeromorphicOn f U) :
  h₁f.inv.divisor = -h₁f.divisor := by
  ext z
  by_cases hz : z ∈ U
  · simp only [hz, eval_of_divisor_outside_domain, DivisorOn.coe_neg, Pi.neg_apply]
    rw [MeromorphicAt.order_inv]
    simp
  · simp [hz]

end MeromorphicOn
