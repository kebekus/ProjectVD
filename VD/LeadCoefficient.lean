/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Order
import VD.ToMathlib.MeromorphicAt_order

/-!
# The Leading Coefficient of a Meromorphic Function

This file defines the leading coefficient of a meromorphic function. If `f` is
meromorphic at a point `x`, the leading coefficient is defined as the (unique!)
value `g x` for a presentation of `f` in the form `(z - x) ^ order • g z` with
`g` analytic at `x`.

### TODOs

- Characterization in terms of limits
- Characterization in terms of Laurent series
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {x : 𝕜} {n : ℤ}

open Filter Topology

variable (f x) in
/--
If `f` is meromorphic of finite order at a point `x`, the leading coefficient is
defined as the (unique!) value `g x` for a presentation of `f` in the form `(z -
x) ^ order • g z` with `g` analytic at `x`. In all other cases, the leading
coefficient is defined to be zero.
-/
noncomputable def leadCoefficient : E := by
  by_cases h₁ : ¬MeromorphicAt f x
  · exact 0
  rw [not_not] at h₁
  by_cases h₂ : h₁.order = ⊤
  · exact 0
  exact (h₁.order_ne_top_iff.1 h₂).choose x

/--
If `f` is not meromorphic at `x`, the leading coefficient is zero by definition.
-/
@[simp] lemma leadCoefficient_of_not_MeromorphicAt (h : ¬MeromorphicAt f x) :
    leadCoefficient f x = 0 := by simp_all [leadCoefficient]

/--
If `f` is meromorphic of infinite order at `x`, the leading coefficient is zero
by definition.
-/
@[simp] lemma leadCoefficient_of_order_eq_top (h₁ : MeromorphicAt f x) (h₂ : h₁.order = ⊤) :
    leadCoefficient f x = 0 := by simp_all [leadCoefficient]

/-!
## Characterization of the Leading Coefficient
-/

/--
Definition of the leading coefficient in case where `f` is meromorphic of finite
order and a presentation is given.
-/
lemma leadCoefficient_of_order_eq_finite (h₁ : MeromorphicAt f x) (h₂ : AnalyticAt 𝕜 g x)
    (h₃ : h₁.order ≠ ⊤) (h₄ : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ h₁.order.untop₀ • g z) :
    leadCoefficient f x = g x := by
  unfold leadCoefficient
  simp only [h₁, not_true_eq_false, reduceDIte, h₃, ne_eq]
  obtain ⟨h'₁, h'₂, h'₃⟩ := (h₁.order_ne_top_iff.1 h₃).choose_spec
  apply Filter.EventuallyEq.eq_of_nhds
  rw [← h'₁.continuousAt.eventuallyEq_nhd_iff_eventuallyEq_nhdNE h₂.continuousAt]
  filter_upwards [h₄, h'₃, self_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [← sub_eq_zero]
  rwa [h₂y, ← sub_eq_zero, ← smul_sub, smul_eq_zero_iff_right] at h₁y
  simp_all [zpow_ne_zero, sub_ne_zero]

/--
Variant of `leadCoefficient_of_order_eq_finite`: Definition of the leading
coefficient in case where `f` is meromorphic of finite order and a presentation
is given.
-/
lemma leadCoefficient_of_order_eq_finite₁ (h₁ : AnalyticAt 𝕜 g x) (h₂ : g x ≠ 0)
    (h₃ : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n • g z) :
    leadCoefficient f x = g x := by
  have h₄ : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h₃]
    fun_prop
  have : h₄.order = n := by
    apply h₄.order_eq_int_iff.2
    simp only [ne_eq, zpow_natCast]
    use g, h₁, h₂
    exact h₃
  apply leadCoefficient_of_order_eq_finite h₄ h₁ (by simp [this]) (by simp_all [this])

/-!
## Elementary Properties
-/

/--
If `f` is meromorphic of finite order at `x`, the leading coefficient is never zero.
-/
lemma leadCoefficient_ne_zero (h₁ : MeromorphicAt f x) (h₂ : h₁.order ≠ ⊤) :
    leadCoefficient f x ≠ 0 := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁.order_ne_top_iff.1 h₂
  rwa [leadCoefficient_of_order_eq_finite₁ h₁g h₂g h₃g]

/-!
## Congruence Lemmata
-/

/--
If two functions agree in a pointed neighborhood, then their leading coefficients agree.
-/
lemma leadCoefficient_congr_nhdNE {f₁ f₂ : 𝕜 → E} (h : f₁ =ᶠ[𝓝[≠] x] f₂) :
    leadCoefficient f₁ x = leadCoefficient f₂ x := by
  by_cases h₁ : ¬MeromorphicAt f₁ x
  · simp [h₁, (MeromorphicAt.meromorphicAt_congr h).not.1 h₁]
  rw [not_not] at h₁
  by_cases h₂ : h₁.order = ⊤
  · simp_all [h₁.congr h, h₁.order_congr h]
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁.order_ne_top_iff.1 h₂
  rw [leadCoefficient_of_order_eq_finite₁ h₁g h₂g h₃g,
    leadCoefficient_of_order_eq_finite₁ h₁g h₂g (h.symm.trans h₃g)]

/-!
## Behavior under Arithmetic Operations
-/

/--
The leading coefficient of a scalar product is the scalar product of the leading coefficients.
-/
lemma leadCoefficient_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E} (hf₁ : MeromorphicAt f₁ x)
    (hf₂ : MeromorphicAt f₂ x) :
    leadCoefficient (f₁ • f₂) x = (leadCoefficient f₁ x) • (leadCoefficient f₂ x) := by
  by_cases h₁f₁ : hf₁.order = ⊤
  · simp_all [hf₁, hf₁.smul hf₂, hf₁.order_smul hf₂, h₁f₁]
  by_cases h₁f₂ : hf₂.order = ⊤
  · simp_all [hf₁, hf₁.smul hf₂, hf₁.order_smul hf₂, h₁f₁]
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := hf₁.order_ne_top_iff.1 h₁f₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := hf₂.order_ne_top_iff.1 h₁f₂
  have : f₁ • f₂ =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ (hf₁.smul hf₂).order.untop₀ • (g₁ • g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with y h₁y h₂y h₃y
    simp_all [hf₁.order_smul hf₂]
    rw [← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul, zpow_add₀ (sub_ne_zero.2 h₃y)]
    ring_nf
  rw [leadCoefficient_of_order_eq_finite₁ h₁g₁ h₂g₁ h₃g₁,
    leadCoefficient_of_order_eq_finite₁ h₁g₂ h₂g₂ h₃g₂,
    leadCoefficient_of_order_eq_finite (hf₁.smul hf₂) (h₁g₁.smul h₁g₂) (by simp_all [hf₁.order_smul hf₂]) this]
  simp

/--
The leading coefficient of a product is the product of the leading coefficients.
-/
lemma leadCoefficient_mul {f₁ f₂ : 𝕜 → 𝕜} (hf₁ : MeromorphicAt f₁ x)
    (hf₂ : MeromorphicAt f₂ x) :
    leadCoefficient (f₁ * f₂) x = (leadCoefficient f₁ x) * (leadCoefficient f₂ x) := by
  exact leadCoefficient_smul hf₁ hf₂
