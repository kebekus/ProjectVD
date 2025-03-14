/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.Divisor.Basic
import VD.meromorphicAt

open Classical

/-!
# The Divisor of a Meromorphic Function

This file defines the divisor of a meromorphic function and proves the most
basic lemmas about those divisors.

## TODO

- Remove the assumption `CompleteSpace E`.
- Compatibility with restriction of divisors/functions
- Non-negativity of the divisor for an analytic function
- Behavior under addition of functions
- Congruence lemmas for `codiscreteWithin`
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {U : Set 𝕜}
  {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

namespace MeromorphicOn

/-!
## Definition of the Divisor
-/

/-- The divisor of a meromorphic function `f`, mapping a point `z` to the order
  of `f` at `z`, and to zero if the order is infinite. -/
noncomputable def divisor (f : 𝕜 → E) (hf : MeromorphicOn f U) :
    DivisorOn U where
  toFun := fun z ↦ if hz : z ∈ U then ((hf z hz).order.untopD 0) else 0
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
      exists_eq_right, Pi.zero_apply, dite_eq_right_iff, WithTop.untopD_eq_self_iff,
      WithTop.coe_zero]
    tauto

/-- Definition of the divisor. -/
theorem divisorOn_def {f : 𝕜 → E} (hf : MeromorphicOn f U) :
    divisor f hf z = if hz : z ∈ U then (hf z hz).order.untopD 0 else 0 := by rfl

/-- Simplifier lemma: A divisor on `U` evaluates to zero outside of `U`. -/
@[simp]
lemma eval_outside_domain (D : DivisorOn U) (hz : z ∉ U) :
    D z = 0 := Function.nmem_support.mp fun a ↦ hz (D.supportWithinDomain a)

/-- Simplifier lemma: On `U`, the divisor of a function `f` that is meromorphic
on `U` evaluates to `order.toBase`. -/
@[simp]
lemma divisorOn_eval_outside_domain {f : 𝕜 → E} (hf : MeromorphicOn f U) (hz : z ∈ U) :
    divisor f hf z = (hf z hz).order.untopD 0 := by simp_all [hf.divisorOn_def, hz]

/-!
## Behavior under Standard Operations
-/

/-- If orders are finite, the divisor of the scalar product of two meromorphic
  functions is the sum of the divisors.

  See `MeromorphicOn.exists_order_ne_top_iff_forall` and
  `MeromorphicOn.order_ne_top_of_isPreconnected` for two convenient criteria to
  guarantee conditions `h₂f₁` and `h₂f₂`.
-/
theorem divisorOn_smul [CompleteSpace 𝕜] {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z, (hz : z ∈ U) → (h₁f₁ z hz).order ≠ ⊤)
    (h₂f₂ : ∀ z, (hz : z ∈ U) → (h₁f₂ z hz).order ≠ ⊤) :
    divisor (f₁ • f₂) (h₁f₁.smul h₁f₂) = divisor f₁ h₁f₁ + divisor f₂ h₁f₂ := by
  ext z
  by_cases hz : z ∈ U
  · simp_all [(h₁f₁ z hz).order_smul (h₁f₂ z hz)]
    lift (h₁f₁ z hz).order to ℤ using (h₂f₁ z hz) with a₁ ha₁
    lift (h₁f₂ z hz).order to ℤ using (h₂f₂ z hz) with a₂ ha₂
    exact rfl
  · simp [hz]

/-- If orders are finite, the divisor of the product of two meromorphic
  functions is the sum of the divisors.

  See `MeromorphicOn.exists_order_ne_top_iff_forall` and
  `MeromorphicOn.order_ne_top_of_isPreconnected` for two convenient criteria to
  guarantee conditions `h₂f₁` and `h₂f₂`.
-/
theorem divisorOn_mul [CompleteSpace 𝕜] {f₁ f₂ : 𝕜 → 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z, (hz : z ∈ U) → (h₁f₁ z hz).order ≠ ⊤)
    (h₂f₂ : ∀ z, (hz : z ∈ U) → (h₁f₂ z hz).order ≠ ⊤) :
    divisor (f₁ * f₂) (h₁f₁.mul h₁f₂) = divisor f₁ h₁f₁ + divisor f₂ h₁f₂ := by
  ext z
  by_cases hz : z ∈ U
  · simp_all [(h₁f₁ z hz).order_mul (h₁f₂ z hz)]
    lift (h₁f₁ z hz).order to ℤ using (h₂f₁ z hz) with a₁ ha₁
    lift (h₁f₂ z hz).order to ℤ using (h₂f₂ z hz) with a₂ ha₂
    exact rfl
  · simp [hz]

/-- The divisor of the inverse is the negative of the divisor. -/
theorem divisorOn_inv [CompleteSpace 𝕜] {f: 𝕜 → 𝕜} (h₁f : MeromorphicOn f U) :
    divisor f⁻¹ h₁f.inv = -divisor f h₁f := by
  ext z
  by_cases hz : z ∈ U
  · simp only [hz, divisorOn_eval_outside_domain, DivisorOn.coe_neg, Pi.neg_apply]
    rw [(h₁f z hz).order_inv]
    by_cases ha : (h₁f z hz).inv.order = ⊤
    · simp only [ha, WithTop.untopD_top, LinearOrderedAddCommGroupWithTop.neg_top, neg_zero]
    lift (h₁f z hz).inv.order to ℤ using ha with a ha
    rw [(by rfl : -a = (↑(-a) : WithTop ℤ)), WithTop.untopD_coe, WithTop.untopD_coe]
    simp
  · simp [hz]

end MeromorphicOn
