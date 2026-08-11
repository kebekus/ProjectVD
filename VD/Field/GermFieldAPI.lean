/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import VD.Field.GermField

/-!
# Supporting API for the Field of Meromorphic Functions

This file provides the basic objects attached to the ring `MeromorphicOn.germRing 𝕜 U` of
meromorphic germs:

- `MeromorphicOn.GermRing.constRingHom`: the embedding of constants, and the associated
  `Algebra 𝕜` instance;
- `MeromorphicOn.GermRing.orderAt`: the order of a germ at a point of `U`, additive on products;
- `MeromorphicOn.GermRing.divisor`: the divisor of a germ, additive on products of nonzero germs;
- `MeromorphicOn.GermRing.toNF`: the canonical representative of a germ, in normal form. On an
  open set, this is the unique normal-form representative, up to values outside of `U`. Since
  functions in normal form are not stable under addition or multiplication, this is a section of
  `MeromorphicOn.toGermRingHom` as a map of sets, not a ring homomorphism.

The definitions choose a meromorphic representative of the germ; the accompanying congruence
lemmas show independence of that choice on preperfect sets.
-/

open Filter Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {f g : 𝕜 → 𝕜} {x : 𝕜}

namespace MeromorphicOn.GermRing

/-!
## Choice of Representatives
-/

/-- A choice of meromorphic representative of a germ in `germRing 𝕜 U`. -/
noncomputable def out (a : germRing 𝕜 U) : 𝕜 → 𝕜 := (mem_germRing_iff.1 a.2).choose

/-- The chosen representative is meromorphic on `U`. -/
theorem meromorphicOn_out (a : germRing 𝕜 U) : MeromorphicOn (out a) U :=
  (mem_germRing_iff.1 a.2).choose_spec.1

@[simp]
theorem coe_out (a : germRing 𝕜 U) :
    ((out a : 𝕜 → 𝕜) : Germ (codiscreteWithin U) 𝕜) = a :=
  (mem_germRing_iff.1 a.2).choose_spec.2

/-- Any representative of a germ agrees with the chosen one along `codiscreteWithin U`. -/
theorem out_eventuallyEq {a : germRing 𝕜 U}
    (hfa : (f : Germ (codiscreteWithin U) 𝕜) = a) : f =ᶠ[codiscreteWithin U] out a :=
  Germ.coe_eq.1 (by rw [hfa, coe_out])

/-!
## The Embedding of Constants
-/

/-- The ring homomorphism mapping a constant to its germ. -/
def constRingHom (𝕜 : Type*) [NontriviallyNormedField 𝕜] (U : Set 𝕜) : 𝕜 →+* germRing 𝕜 U :=
  ((Germ.coeRingHom _).comp (Pi.constRingHom 𝕜 𝕜)).codRestrict _
    fun c ↦ coe_mem_germRing (const c)

@[simp]
theorem coe_constRingHom (c : 𝕜) :
    ((constRingHom 𝕜 U c : germRing 𝕜 U) : Germ (codiscreteWithin U) 𝕜) =
      ((fun _ ↦ c : 𝕜 → 𝕜) : Germ (codiscreteWithin U) 𝕜) :=
  rfl

/-- If `codiscreteWithin U` is nontrivial, distinct constants have distinct germs. -/
theorem constRingHom_injective (h : (codiscreteWithin U).NeBot) :
    Function.Injective (constRingHom 𝕜 U) := by
  intro c d hcd
  obtain ⟨x, hx⟩ := (Germ.coe_eq.1 (congrArg Subtype.val hcd)).exists
  exact hx

/-- The ring of meromorphic germs is a `𝕜`-algebra, with constants acting as scalars. -/
noncomputable instance : Algebra 𝕜 (germRing 𝕜 U) := (constRingHom 𝕜 U).toAlgebra

theorem algebraMap_eq_constRingHom :
    algebraMap 𝕜 (germRing 𝕜 U) = constRingHom 𝕜 U := rfl

/-!
## Order at a Point
-/

/-- The order of a meromorphic germ at a point, defined as the order of the chosen
representative. On preperfect sets, this is the order of any representative, see
`MeromorphicOn.GermRing.orderAt_coe`. -/
noncomputable def orderAt (a : germRing 𝕜 U) (x : 𝕜) : WithTop ℤ :=
  meromorphicOrderAt (out a) x

/-- On preperfect sets, the order of a germ at a point of `U` equals the order of any
meromorphic representative. -/
theorem orderAt_coe (hU : Preperfect U) (hf : MeromorphicOn f U) (hx : x ∈ U)
    {a : germRing 𝕜 U} (hfa : (f : Germ (codiscreteWithin U) 𝕜) = a) :
    orderAt a x = meromorphicOrderAt f x :=
  (meromorphicOrderAt_congr
    ((hf x hx).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (meromorphicOn_out a x hx) hx hU (out_eventuallyEq hfa))).symm

/-- The order at points of a preperfect set is additive on products of germs. -/
theorem orderAt_mul (hU : Preperfect U) (hx : x ∈ U) (a b : germRing 𝕜 U) :
    orderAt (a * b) x = orderAt a x + orderAt b x := by
  rw [orderAt_coe hU ((meromorphicOn_out a).mul (meromorphicOn_out b)) hx
    (by push_cast [coe_out]; rfl)]
  exact meromorphicOrderAt_mul (meromorphicOn_out a x hx) (meromorphicOn_out b x hx)

/-- On a preperfect set, a germ vanishes iff its order is infinite at every point of `U`. -/
theorem eq_zero_iff_forall_orderAt_eq_top (hU : Preperfect U) {a : germRing 𝕜 U} :
    a = 0 ↔ ∀ x ∈ U, orderAt a x = ⊤ := by
  rw [Subtype.ext_iff, ← coe_out a]
  exact coe_eq_zero_iff (meromorphicOn_out a) hU

/-- On a preconnected set with at least two points, nonzero germs have finite order at every
point of `U`. In particular, `orderAt · x` restricts to a `ℤ`-valued valuation on the field of
meromorphic germs. -/
theorem orderAt_ne_top (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) {a : germRing 𝕜 U}
    (ha : a ≠ 0) (hx : x ∈ U) : orderAt a x ≠ ⊤ := by
  have hU := h₁U.preperfect_of_nontrivial h₂U
  have h : ¬∀ y ∈ U, orderAt a y = ⊤ := fun h ↦ ha ((eq_zero_iff_forall_orderAt_eq_top hU).2 h)
  push Not at h
  obtain ⟨y, hy, hne⟩ := h
  exact ((meromorphicOn_out a).exists_meromorphicOrderAt_ne_top_iff_forall_mem
    ⟨h₂U.nonempty, h₁U⟩).1 ⟨y, hy, hne⟩ x hx

/-!
## The Divisor of a Germ
-/

/-- The divisor of a meromorphic germ, defined as the divisor of the chosen representative. On
preperfect sets, this is the divisor of any representative, see
`MeromorphicOn.GermRing.divisor_coe`. -/
noncomputable def divisor (a : germRing 𝕜 U) : Function.locallyFinsuppWithin U ℤ :=
  MeromorphicOn.divisor (out a) U

/-- On preperfect sets, the divisor of a germ equals the divisor of any meromorphic
representative. -/
theorem divisor_coe (hU : Preperfect U) (hf : MeromorphicOn f U) {a : germRing 𝕜 U}
    (hfa : (f : Germ (codiscreteWithin U) 𝕜) = a) :
    divisor a = MeromorphicOn.divisor f U :=
  divisor_of_eventuallyEq_codiscreteWithin_preperfect (meromorphicOn_out a) hf hU
    (out_eventuallyEq hfa).symm

/-- On a preconnected set with at least two points, the divisor is additive on products of
nonzero germs. In particular, it restricts to a group homomorphism on the units of the field of
meromorphic germs. -/
theorem divisor_mul (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) {a b : germRing 𝕜 U}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    divisor (a * b) = divisor a + divisor b := by
  have hU := h₁U.preperfect_of_nontrivial h₂U
  rw [divisor_coe hU ((meromorphicOn_out a).mul (meromorphicOn_out b))
    (by push_cast [coe_out]; rfl)]
  exact MeromorphicOn.divisor_mul (meromorphicOn_out a) (meromorphicOn_out b)
    (fun z hz ↦ orderAt_ne_top h₁U h₂U ha hz) (fun z hz ↦ orderAt_ne_top h₁U h₂U hb hz)

/-- On a preperfect set, the divisor of the inverse germ is the negative of the divisor. -/
theorem divisor_inv (hU : Preperfect U) (a : germRing 𝕜 U) : divisor a⁻¹ = -divisor a := by
  rw [divisor_coe hU (meromorphicOn_out a).inv (by rw [Germ.coe_inv, coe_out, coe_inv])]
  exact MeromorphicOn.divisor_inv

/-!
## The Normal Form Representative
-/

/-- The canonical representative of a meromorphic germ: the normal form of the chosen
representative. On open sets, this is the unique representative in normal form, up to values
outside of `U`, see `MeromorphicOn.GermRing.eqOn_toNF_of_meromorphicNFOn`.

Since functions in normal form are not stable under addition or multiplication, `toNF` is a
section of `MeromorphicOn.toGermRingHom` as a map of sets, not a ring homomorphism. -/
noncomputable def toNF (a : germRing 𝕜 U) : 𝕜 → 𝕜 := toMeromorphicNFOn (out a) U

/-- The canonical representative is in normal form. -/
theorem meromorphicNFOn_toNF (a : germRing 𝕜 U) : MeromorphicNFOn (toNF a) U :=
  meromorphicNFOn_toMeromorphicNFOn (out a) U

/-- The canonical representative represents the germ. -/
@[simp]
theorem coe_toNF (a : germRing 𝕜 U) :
    ((toNF a : 𝕜 → 𝕜) : Germ (codiscreteWithin U) 𝕜) = a := by
  rw [← coe_out a]
  exact (Germ.coe_eq.2 (toMeromorphicNFOn_eqOn_codiscrete (meromorphicOn_out a))).symm

/-- The map `toNF` is a section of the quotient map `toGermRingHom`. -/
theorem toGermRingHom_toNF (a : germRing 𝕜 U) :
    toGermRingHom ⟨toNF a, (meromorphicNFOn_toNF a).meromorphicOn⟩ = a :=
  Subtype.ext (coe_toNF a)

/-- On open sets, any normal-form representative of a germ agrees with the canonical
representative on `U`. Off `U`, representatives of the germ are unconstrained, so this is the
strongest possible uniqueness statement. -/
theorem eqOn_toNF_of_meromorphicNFOn (hU : IsOpen U) {a : germRing 𝕜 U}
    (h₁g : MeromorphicNFOn g U) (h₂g : (g : Germ (codiscreteWithin U) 𝕜) = a) :
    Set.EqOn g (toNF a) U := by
  intro x hx
  have h₁ : g =ᶠ[codiscreteWithin U] toNF a := Germ.coe_eq.1 (by rw [h₂g, coe_toNF])
  have h₂ : g =ᶠ[𝓝[≠] x] toNF a :=
    (eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE hU).1 h₁ x hx
  have h₃ : g =ᶠ[𝓝 x] toNF a :=
    ((h₁g hx).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (meromorphicNFOn_toNF a hx)).1 h₂
  exact h₃.eq_of_nhds

end MeromorphicOn.GermRing
