/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Order.Filter.Germ.Basic
import VD.Field.CodiscreteWithinNeBot
import VD.Field.MeromorphicGermZero

/-!
# The Field of Meromorphic Functions on a Connected Set

Functions meromorphic on a set `U` form a subring `MeromorphicOn.subring 𝕜 U` of the ring of all
functions `𝕜 → 𝕜`. This ring is never a field: functions supported on discrete sets are zero
divisors. Passing to germs with respect to the filter `Filter.codiscreteWithin U` remedies this:
the image `MeromorphicOn.germRing 𝕜 U` of the subring in the germ ring carries a natural
pointwise inverse, and if `U` is preconnected with at least two points, it is a field, with
instance `MeromorphicOn.GermRing.instField` available under `Fact` assumptions on `U`.

The key input is the identity theorem for meromorphic functions: on a preconnected set, a
meromorphic function whose germ is nonzero has finite order everywhere
(`MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall`), so its zero set is codiscrete
within `U` and the pointwise inverse is a genuine inverse
(`MeromorphicOn.self_mul_inv_eventuallyEq_one_codiscreteWithin`).
-/

open Filter Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {f : 𝕜 → 𝕜}

namespace MeromorphicOn

/-!
## The Ring of Meromorphic Functions
-/

/-- Functions meromorphic on `U`, as a subring of the ring of all functions `𝕜 → 𝕜`. -/
def subring (𝕜 : Type*) [NontriviallyNormedField 𝕜] (U : Set 𝕜) : Subring (𝕜 → 𝕜) where
  carrier := {f | MeromorphicOn f U}
  zero_mem' := const 0
  one_mem' := const 1
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  neg_mem' hf := hf.neg

@[simp]
theorem mem_subring_iff : f ∈ subring 𝕜 U ↔ MeromorphicOn f U := Iff.rfl

/-!
## The Ring of Meromorphic Germs
-/

/--
Germs of meromorphic functions with respect to the filter `codiscreteWithin U`, as a subring of
the ring of all germs. If `U` is preconnected with at least two points, this ring is a field, see
`MeromorphicOn.GermRing.instField`.
-/
def germRing (𝕜 : Type*) [NontriviallyNormedField 𝕜] (U : Set 𝕜) :
    Subring (Germ (codiscreteWithin U) 𝕜) :=
  (subring 𝕜 U).map (Germ.coeRingHom _)

/-- Membership in `germRing 𝕜 U` means: the germ has a meromorphic representative. -/
theorem mem_germRing_iff {γ : Germ (codiscreteWithin U) 𝕜} :
    γ ∈ germRing 𝕜 U ↔ ∃ f : 𝕜 → 𝕜, MeromorphicOn f U ∧ (f : Germ (codiscreteWithin U) 𝕜) = γ :=
  ⟨fun ⟨f, hf, h⟩ ↦ ⟨f, hf, h⟩, fun ⟨f, hf, h⟩ ↦ ⟨f, hf, h⟩⟩

/-- The germ of a meromorphic function lies in `germRing 𝕜 U`. -/
theorem coe_mem_germRing (hf : MeromorphicOn f U) :
    (f : Germ (codiscreteWithin U) 𝕜) ∈ germRing 𝕜 U :=
  mem_germRing_iff.2 ⟨f, hf, rfl⟩

/-- The surjective ring homomorphism mapping a meromorphic function to its germ. -/
def toGermRingHom : subring 𝕜 U →+* germRing 𝕜 U :=
  ((Germ.coeRingHom _).comp (subring 𝕜 U).subtype).codRestrict _
    fun f ↦ coe_mem_germRing f.2

theorem toGermRingHom_surjective :
    Function.Surjective (toGermRingHom (𝕜 := 𝕜) (U := U)) := by
  rintro ⟨γ, hγ⟩
  obtain ⟨f, hf, rfl⟩ := mem_germRing_iff.1 hγ
  exact ⟨⟨f, hf⟩, rfl⟩

namespace GermRing

/-!
## Inverses in the Ring of Meromorphic Germs

The ring of meromorphic germs inherits the pointwise inverse of germs, using the junk-value
convention `(0 : 𝕜)⁻¹ = 0`: the inverse of a function meromorphic on `U` is meromorphic on `U`,
so the subring is closed under `Inv` without any hypotheses on `U`.
-/

noncomputable instance : Inv (germRing 𝕜 U) where
  inv a := ⟨(a : Germ (codiscreteWithin U) 𝕜)⁻¹, by
    obtain ⟨f, hf, hfa⟩ := mem_germRing_iff.1 a.2
    exact mem_germRing_iff.2 ⟨f⁻¹, hf.inv, by rw [Germ.coe_inv, hfa]⟩⟩

@[simp, norm_cast]
theorem coe_inv (a : germRing 𝕜 U) :
    ((a⁻¹ : germRing 𝕜 U) : Germ (codiscreteWithin U) 𝕜) = (a : Germ (codiscreteWithin U) 𝕜)⁻¹ :=
  rfl

noncomputable instance : Div (germRing 𝕜 U) where
  div a b := a * b⁻¹

theorem div_eq_mul_inv (a b : germRing 𝕜 U) : a / b = a * b⁻¹ := rfl

@[simp, norm_cast]
theorem coe_div (a b : germRing 𝕜 U) :
    ((a / b : germRing 𝕜 U) : Germ (codiscreteWithin U) 𝕜) =
      (a : Germ (codiscreteWithin U) 𝕜) / (b : Germ (codiscreteWithin U) 𝕜) := by
  rw [div_eq_mul_inv, division_def]
  push_cast
  rfl

protected theorem inv_zero : (0 : germRing 𝕜 U)⁻¹ = 0 := by
  apply Subtype.ext
  rw [coe_inv]
  change ((0 : 𝕜 → 𝕜) : Germ (codiscreteWithin U) 𝕜)⁻¹ = ((0 : 𝕜 → 𝕜) : Germ _ 𝕜)
  rw [← Germ.coe_inv, Germ.coe_eq]
  filter_upwards with x
  simp

/-!
## Nontriviality and the Field Structure
-/

/-- The ring of meromorphic germs is nontrivial whenever `codiscreteWithin U` is nontrivial. -/
theorem nontrivial (h : (codiscreteWithin U).NeBot) : Nontrivial (germRing 𝕜 U) := by
  refine ⟨0, 1, fun hcon ↦ ?_⟩
  have h₂ : ((0 : 𝕜 → 𝕜) : Germ (codiscreteWithin U) 𝕜) = ((1 : 𝕜 → 𝕜) : Germ _ 𝕜) :=
    congrArg Subtype.val hcon
  obtain ⟨x, hx⟩ := (Germ.coe_eq.1 h₂).exists
  exact zero_ne_one (α := 𝕜) hx

instance [h₁U : Fact (IsPreconnected U)] [h₂U : Fact U.Nontrivial] :
    Nontrivial (germRing 𝕜 U) :=
  nontrivial (h₁U.out.codiscreteWithin_neBot h₂U.out)

/--
The germ of a function meromorphic on a preperfect set `U` vanishes iff the function has
infinite order at every point of `U`.
-/
theorem coe_eq_zero_iff (hf : MeromorphicOn f U) (hU : Preperfect U) :
    (f : Germ (codiscreteWithin U) 𝕜) = 0 ↔ ∀ x ∈ U, meromorphicOrderAt f x = ⊤ := by
  rw [show (0 : Germ (codiscreteWithin U) 𝕜) = ((0 : 𝕜 → 𝕜) : Germ _ 𝕜) from rfl, Germ.coe_eq]
  exact hf.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top hU

/--
On a preconnected set with at least two points, every nonzero meromorphic germ is invertible,
with the pointwise inverse as its inverse.
-/
protected theorem mul_inv_cancel (h₁U : IsPreconnected U) (h₂U : U.Nontrivial)
    {a : germRing 𝕜 U} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  obtain ⟨f, hf, hfa⟩ := mem_germRing_iff.1 a.2
  have horder : ∀ x ∈ U, meromorphicOrderAt f x ≠ ⊤ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, h₁x, h₂x⟩ := hcon
    apply ha
    apply Subtype.ext
    rw [← hfa]
    exact (coe_eq_zero_iff hf (h₁U.preperfect_of_nontrivial h₂U)).2
      ((hf.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top
        (h₁U.preperfect_of_nontrivial h₂U)).1
        ((hf.eventuallyEq_zero_codiscreteWithin_iff_exists_meromorphicOrderAt_eq_top
          h₁U h₂U).2 ⟨x, h₁x, h₂x⟩))
  apply Subtype.ext
  push_cast
  rw [← hfa, ← Germ.coe_inv, ← Germ.coe_mul,
    show (1 : Germ (codiscreteWithin U) 𝕜) = ((1 : 𝕜 → 𝕜) : Germ _ 𝕜) from rfl, Germ.coe_eq]
  exact hf.self_mul_inv_eventuallyEq_one_codiscreteWithin horder

/-- On a preconnected set with at least two points, the ring of meromorphic germs is a field. -/
theorem isField (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) : IsField (germRing 𝕜 U) where
  exists_pair_ne := (nontrivial (h₁U.codiscreteWithin_neBot h₂U)).exists_pair_ne
  mul_comm := mul_comm
  mul_inv_cancel ha := ⟨_, GermRing.mul_inv_cancel h₁U h₂U ha⟩

/--
The field of meromorphic functions on a preconnected set with at least two points: field
instance for the ring of meromorphic germs, with the pointwise inverse.
-/
noncomputable instance instField [h₁U : Fact (IsPreconnected U)] [h₂U : Fact U.Nontrivial] :
    Field (germRing 𝕜 U) where
  __ := (inferInstance : CommRing (germRing 𝕜 U))
  inv := Inv.inv
  div := Div.div
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := exists_pair_ne _
  mul_inv_cancel _ ha := GermRing.mul_inv_cancel h₁U.out h₂U.out ha
  inv_zero := GermRing.inv_zero
  nnqsmul := _
  qsmul := _

/-- On a preconnected set with at least two points, the ring of meromorphic germs is a domain. -/
theorem isDomain (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) : IsDomain (germRing 𝕜 U) :=
  have : Fact (IsPreconnected U) := ⟨h₁U⟩
  have : Fact U.Nontrivial := ⟨h₂U⟩
  inferInstance

end GermRing

end MeromorphicOn
