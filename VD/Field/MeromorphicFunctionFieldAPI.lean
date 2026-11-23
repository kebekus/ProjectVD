/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.NormalForm
public import VD.Field.MeromorphicFunctionField
public import VD.MathlibSubmitted.MeromorphicGermZero

/-!
# Supporting API for the Field of Meromorphic Functions

This file provides the basic objects attached to the ring `MeromorphicOn.functionRing 𝕜 𝕜' U` of
meromorphic functions on `U`:

- `MeromorphicOn.FunctionRing.mk`: the element represented by a function meromorphic on `U`, and
  `Meromorphic.toFunctionRing`, its counterpart for functions meromorphic on all of `𝕜`;
- `MeromorphicOn.FunctionRing.constRingHom`: the embedding of constants in `𝕜'`;
- `MeromorphicOn.FunctionRing.orderAt`: the order at a point of `U`, additive on products;
- `MeromorphicOn.FunctionRing.divisor`: the divisor, additive on products of nonzero elements;
- `MeromorphicOn.FunctionRing.toNF`: the canonical representative, in normal form. On an open set,
  this is the unique normal-form representative, up to values outside of `U`. Since functions in
  normal form are not stable under addition or multiplication, this is a section of
  `MeromorphicOn.toFunctionRingAlgHom` as a map of sets, not an algebra homomorphism.

For `U = univ`, the file provides the `Fact` instances that make `functionRing 𝕜 𝕜' univ` a field
whenever `𝕜` is preconnected.

The definitions choose a meromorphic representative of each element; the accompanying congruence
lemmas show independence of that choice on preperfect sets.
-/

@[expose] public section

open Filter Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {𝕜' : Type*} [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {U : Set 𝕜} {f g : 𝕜 → 𝕜'} {x : 𝕜}

namespace MeromorphicOn.FunctionRing

/-!
## Choice of Representatives
-/

/-- A choice of meromorphic representative of an element of `functionRing 𝕜 𝕜' U`. -/
noncomputable def out (a : functionRing 𝕜 𝕜' U) : 𝕜 → 𝕜' :=
  (mem_functionRing_iff.1 a.property).choose

/-- The chosen representative is meromorphic on `U`. -/
theorem meromorphicOn_out (a : functionRing 𝕜 𝕜' U) : MeromorphicOn (out a) U :=
  (mem_functionRing_iff.1 a.property).choose_spec.1

@[simp]
theorem coe_out (a : functionRing 𝕜 𝕜' U) :
    ((out a : 𝕜 → 𝕜') : Germ (codiscreteWithin U) 𝕜') = a :=
  (mem_functionRing_iff.1 a.property).choose_spec.2

/-- Any representative of an element agrees with the chosen one along `codiscreteWithin U`. -/
theorem out_eventuallyEq {a : functionRing 𝕜 𝕜' U}
    (hfa : (f : Germ (codiscreteWithin U) 𝕜') = a) : f =ᶠ[codiscreteWithin U] out a :=
  Germ.coe_eq.1 (by rw [hfa, coe_out])

/-- An element vanishes if and only if its chosen representative is zero along
`codiscreteWithin U`. -/
theorem eq_zero_iff_out_eventuallyEq_zero {a : functionRing 𝕜 𝕜' U} :
    a = 0 ↔ out a =ᶠ[codiscreteWithin U] 0 := by
  rw [Subtype.ext_iff, ← coe_out a, ← Germ.coe_eq]
  rfl

/-!
## The Element Represented by a Meromorphic Function
-/

/-- The element of `functionRing 𝕜 𝕜' U` represented by a function meromorphic on `U`. -/
def mk (hf : MeromorphicOn f U) : functionRing 𝕜 𝕜' U :=
  ⟨(f : Germ (codiscreteWithin U) 𝕜'), coe_mem_functionRing hf⟩

@[simp]
theorem coe_mk (hf : MeromorphicOn f U) :
    ((mk hf : functionRing 𝕜 𝕜' U) : Germ (codiscreteWithin U) 𝕜') = f :=
  rfl

/-- A meromorphic function agrees with the chosen representative of the element it represents,
along `codiscreteWithin U`. -/
theorem eventuallyEq_out_mk (hf : MeromorphicOn f U) : f =ᶠ[codiscreteWithin U] out (mk hf) :=
  out_eventuallyEq rfl

/-!
### Representatives of Sums, Products, Powers, Inverses and Constants

The chosen representative of a sum, product, power or inverse of elements agrees with the sum,
product, power or inverse of the chosen representatives along `codiscreteWithin U`.
-/

theorem out_zero : out (0 : functionRing 𝕜 𝕜' U) =ᶠ[codiscreteWithin U] 0 :=
  (out_eventuallyEq (by simp)).symm

theorem out_one : out (1 : functionRing 𝕜 𝕜' U) =ᶠ[codiscreteWithin U] 1 :=
  (out_eventuallyEq (by simp)).symm

theorem out_add (a b : functionRing 𝕜 𝕜' U) : out (a + b) =ᶠ[codiscreteWithin U] out a + out b :=
  (out_eventuallyEq (by simp)).symm

theorem out_neg (a : functionRing 𝕜 𝕜' U) : out (-a) =ᶠ[codiscreteWithin U] -out a :=
  (out_eventuallyEq (by simp)).symm

theorem out_mul (a b : functionRing 𝕜 𝕜' U) : out (a * b) =ᶠ[codiscreteWithin U] out a * out b :=
  (out_eventuallyEq (by simp)).symm

theorem out_pow (a : functionRing 𝕜 𝕜' U) (n : ℕ) : out (a ^ n) =ᶠ[codiscreteWithin U] out a ^ n :=
  (out_eventuallyEq (by simp)).symm

theorem out_inv (a : functionRing 𝕜 𝕜' U) : out a⁻¹ =ᶠ[codiscreteWithin U] (out a)⁻¹ :=
  (out_eventuallyEq (by simp)).symm

/-- Eventual equality is compatible with finite sums. -/
theorem _root_.Filter.EventuallyEq.finset_sum {α ι M : Type*} [AddCommMonoid M] {l : Filter α}
    {s : Finset ι} {f g : ι → α → M} (h : ∀ i ∈ s, f i =ᶠ[l] g i) :
    ∑ i ∈ s, f i =ᶠ[l] ∑ i ∈ s, g i :=
  ((eventually_all_finset s).2 h).mono fun x hx ↦ by
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl hx

theorem out_sum {ι : Type*} (s : Finset ι) (c : ι → functionRing 𝕜 𝕜' U) :
    out (∑ i ∈ s, c i) =ᶠ[codiscreteWithin U] ∑ i ∈ s, out (c i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using out_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (out_add _ _).trans ((EventuallyEq.refl _ _).add ih)

/-!
## The Embedding of Constants
-/

variable (𝕜 U) in
/-- The ring homomorphism mapping a constant to the corresponding constant function. -/
def constRingHom : 𝕜' →+* functionRing 𝕜 𝕜' U :=
  ((Germ.coeRingHom _).comp (Pi.constRingHom 𝕜 𝕜')).codRestrict _
    fun c ↦ coe_mem_functionRing (const c)

@[simp]
theorem coe_constRingHom (c : 𝕜') :
    ((constRingHom 𝕜 U c : functionRing 𝕜 𝕜' U) : Germ (codiscreteWithin U) 𝕜') =
      ((fun _ ↦ c : 𝕜 → 𝕜') : Germ (codiscreteWithin U) 𝕜') :=
  rfl

/-- If `codiscreteWithin U` is nontrivial, the embedding of constants is injective. -/
theorem constRingHom_injective (h : (codiscreteWithin U).NeBot) :
    Function.Injective (constRingHom 𝕜 U (𝕜' := 𝕜')) := by
  intro c d hcd
  obtain ⟨x, hx⟩ := (Germ.coe_eq.1 (congrArg Subtype.val hcd)).exists
  exact hx

/-- The scalars of the `𝕜`-algebra `functionRing 𝕜 𝕜' U` are the constant functions. -/
theorem algebraMap_eq_constRingHom_comp :
    algebraMap 𝕜 (functionRing 𝕜 𝕜' U) = (constRingHom 𝕜 U).comp (algebraMap 𝕜 𝕜') :=
  RingHom.ext fun c ↦ Subtype.ext (Germ.algebraMap_apply c)

/-- The chosen representative of a scalar is the constant function along
`codiscreteWithin U`. -/
theorem out_algebraMap (c : 𝕜) :
    out (algebraMap 𝕜 (functionRing 𝕜 𝕜' U) c) =ᶠ[codiscreteWithin U] fun _ ↦ algebraMap 𝕜 𝕜' c :=
  (out_eventuallyEq (Germ.algebraMap_apply c).symm).symm

/-!
## Order at a Point
-/

/-- The order of an element of `functionRing 𝕜 𝕜' U` at a point, defined as the order of the
chosen representative. On preperfect sets, this is the order of any representative, see
`MeromorphicOn.FunctionRing.orderAt_coe`. -/
noncomputable def orderAt (a : functionRing 𝕜 𝕜' U) (x : 𝕜) : WithTop ℤ :=
  meromorphicOrderAt (out a) x

/-- On preperfect sets, the order of an element at a point of `U` equals the order of any
meromorphic representative. -/
theorem orderAt_coe (hU : Preperfect U) (hf : MeromorphicOn f U) (hx : x ∈ U)
    {a : functionRing 𝕜 𝕜' U} (hfa : (f : Germ (codiscreteWithin U) 𝕜') = a) :
    orderAt a x = meromorphicOrderAt f x :=
  (meromorphicOrderAt_congr
    ((hf x hx).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (meromorphicOn_out a x hx) hx hU (out_eventuallyEq hfa))).symm

/-- The order at points of a preperfect set is additive on products. -/
theorem orderAt_mul (hU : Preperfect U) (hx : x ∈ U) (a b : functionRing 𝕜 𝕜' U) :
    orderAt (a * b) x = orderAt a x + orderAt b x := by
  rw [orderAt_coe hU ((meromorphicOn_out a).mul (meromorphicOn_out b)) hx
    (by push_cast [coe_out]; rfl)]
  exact meromorphicOrderAt_mul (meromorphicOn_out a x hx) (meromorphicOn_out b x hx)

/--
The germ of a function meromorphic on a preperfect set `U` vanishes iff the function has infinite
order at every point of `U`.

This statement depends on Mathlib PR #45423 (`VD/MathlibSubmitted/MeromorphicGermZero.lean`) and
is therefore not part of the PR that upstreams `VD/Field/MeromorphicFunctionField.lean`. It can
follow, together with the rest of this file, once #45423 is merged.
-/
theorem coe_eq_zero_iff (hf : MeromorphicOn f U) (hU : Preperfect U) :
    (f : Germ (codiscreteWithin U) 𝕜') = 0 ↔ ∀ x ∈ U, meromorphicOrderAt f x = ⊤ := by
  rw [show (0 : Germ (codiscreteWithin U) 𝕜') = ((0 : 𝕜 → 𝕜') : Germ _ 𝕜') from rfl, Germ.coe_eq]
  exact hf.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top hU

/-- On a preperfect set, an element vanishes iff its order is infinite at every point of `U`. -/
theorem eq_zero_iff_forall_orderAt_eq_top (hU : Preperfect U) {a : functionRing 𝕜 𝕜' U} :
    a = 0 ↔ ∀ x ∈ U, orderAt a x = ⊤ := by
  rw [Subtype.ext_iff, ← coe_out a]
  exact coe_eq_zero_iff (meromorphicOn_out a) hU

/-- On a preconnected set with at least two points, nonzero elements have finite order at every
point of `U`. In particular, `orderAt · x` restricts to a `ℤ`-valued valuation on the field of
meromorphic functions. -/
theorem orderAt_ne_top (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) {a : functionRing 𝕜 𝕜' U}
    (ha : a ≠ 0) (hx : x ∈ U) : orderAt a x ≠ ⊤ := by
  have hU := h₁U.preperfect_of_nontrivial h₂U
  have h : ¬∀ y ∈ U, orderAt a y = ⊤ := fun h ↦ ha ((eq_zero_iff_forall_orderAt_eq_top hU).2 h)
  push Not at h
  obtain ⟨y, hy, hne⟩ := h
  exact ((meromorphicOn_out a).exists_meromorphicOrderAt_ne_top_iff_forall_mem
    ⟨h₂U.nonempty, h₁U⟩).1 ⟨y, hy, hne⟩ x hx

/-!
### Order of Sums, Powers and Inverses

On preperfect sets, `orderAt · x` behaves like a valuation on the ring of meromorphic functions.
-/

/-- On a preperfect set, the order of an element at a point of `U` equals the order of any
meromorphic function that agrees with the chosen representative along `codiscreteWithin U`. -/
theorem orderAt_eq_of_out_eventuallyEq (hU : Preperfect U) (hx : x ∈ U) {a : functionRing 𝕜 𝕜' U}
    (hf : MeromorphicOn f U) (h : out a =ᶠ[codiscreteWithin U] f) :
    orderAt a x = meromorphicOrderAt f x :=
  orderAt_coe hU hf hx (by rw [← coe_out a]; exact (Germ.coe_eq.2 h).symm)

theorem orderAt_zero (hU : Preperfect U) (hx : x ∈ U) :
    orderAt (0 : functionRing 𝕜 𝕜' U) x = ⊤ := by
  rw [orderAt_eq_of_out_eventuallyEq hU hx (fun z _ ↦ MeromorphicAt.const 0 z) out_zero]
  exact meromorphicOrderAt_eq_top_iff.2 (by simp)

theorem orderAt_one (hU : Preperfect U) (hx : x ∈ U) :
    orderAt (1 : functionRing 𝕜 𝕜' U) x = 0 := by
  classical
  rw [orderAt_eq_of_out_eventuallyEq hU hx (fun z _ ↦ MeromorphicAt.const 1 z) out_one]
  simpa using meromorphicOrderAt_const x (1 : 𝕜')

theorem orderAt_neg (hU : Preperfect U) (hx : x ∈ U) (a : functionRing 𝕜 𝕜' U) :
    orderAt (-a) x = orderAt a x := by
  rw [orderAt_eq_of_out_eventuallyEq hU hx (meromorphicOn_out a).neg (out_neg a)]
  exact meromorphicOrderAt_neg.symm

theorem orderAt_pow (hU : Preperfect U) (hx : x ∈ U) (a : functionRing 𝕜 𝕜' U) (n : ℕ) :
    orderAt (a ^ n) x = n * orderAt a x := by
  rw [orderAt_eq_of_out_eventuallyEq hU hx ((meromorphicOn_out a).pow n) (out_pow a n)]
  exact meromorphicOrderAt_pow (meromorphicOn_out a x hx)

theorem orderAt_inv (hU : Preperfect U) (hx : x ∈ U) (a : functionRing 𝕜 𝕜' U) :
    orderAt a⁻¹ x = -orderAt a x := by
  rw [orderAt_eq_of_out_eventuallyEq hU hx (meromorphicOn_out a).inv (out_inv a)]
  exact meromorphicOrderAt_inv

theorem min_orderAt_le_orderAt_add (hU : Preperfect U) (hx : x ∈ U) (a b : functionRing 𝕜 𝕜' U) :
    min (orderAt a x) (orderAt b x) ≤ orderAt (a + b) x := by
  rw [orderAt_eq_of_out_eventuallyEq hU hx ((meromorphicOn_out a).add (meromorphicOn_out b))
    (out_add a b)]
  exact meromorphicOrderAt_add (meromorphicOn_out a x hx) (meromorphicOn_out b x hx)

/-- If `a` has strictly smaller order than `b` at `x`, then `a + b` has the order of `a`. -/
theorem orderAt_add_eq_left_of_lt (hU : Preperfect U) (hx : x ∈ U) {a b : functionRing 𝕜 𝕜' U}
    (h : orderAt a x < orderAt b x) : orderAt (a + b) x = orderAt a x := by
  rw [orderAt_eq_of_out_eventuallyEq hU hx ((meromorphicOn_out a).add (meromorphicOn_out b))
    (out_add a b)]
  exact meromorphicOrderAt_add_eq_left_of_lt (meromorphicOn_out b x hx) h

/-- The order of a finite sum is at least the minimum of the orders of the summands. -/
theorem le_orderAt_sum (hU : Preperfect U) (hx : x ∈ U) {ι : Type*} {s : Finset ι}
    {c : ι → functionRing 𝕜 𝕜' U} {n : WithTop ℤ} (h : ∀ i ∈ s, n ≤ orderAt (c i) x) :
    n ≤ orderAt (∑ i ∈ s, c i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, orderAt_zero hU hx]
    exact le_top
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact le_trans (le_min (h i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))) (min_orderAt_le_orderAt_add hU hx _ _)

/-!
## The Divisor
-/

/-- The divisor of an element of `functionRing 𝕜 𝕜' U`, defined as the divisor of the chosen
representative. On preperfect sets, this is the divisor of any representative, see
`MeromorphicOn.FunctionRing.divisor_coe`. -/
noncomputable def divisor (a : functionRing 𝕜 𝕜' U) : Function.locallyFinsuppWithin U ℤ :=
  MeromorphicOn.divisor (out a) U

/-- On preperfect sets, the divisor of an element equals the divisor of any meromorphic
representative. -/
theorem divisor_coe (hU : Preperfect U) (hf : MeromorphicOn f U) {a : functionRing 𝕜 𝕜' U}
    (hfa : (f : Germ (codiscreteWithin U) 𝕜') = a) :
    divisor a = MeromorphicOn.divisor f U :=
  divisor_of_eventuallyEq_codiscreteWithin_preperfect (meromorphicOn_out a) hf hU
    (out_eventuallyEq hfa).symm

/-- On a preconnected set with at least two points, the divisor is additive on products of
nonzero elements. In particular, it restricts to a group homomorphism on the units of the field of
meromorphic functions. -/
theorem divisor_mul (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) {a b : functionRing 𝕜 𝕜' U}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    divisor (a * b) = divisor a + divisor b := by
  have hU := h₁U.preperfect_of_nontrivial h₂U
  rw [divisor_coe hU ((meromorphicOn_out a).mul (meromorphicOn_out b))
    (by push_cast [coe_out]; rfl)]
  have hf := meromorphicOn_out a
  have hg := meromorphicOn_out b
  ext z
  by_cases hz : z ∈ U
  · lift meromorphicOrderAt (out a) z to ℤ using orderAt_ne_top h₁U h₂U ha hz with m hm
    lift meromorphicOrderAt (out b) z to ℤ using orderAt_ne_top h₁U h₂U hb hz with n hn
    simp [divisor, hf, hg, hf.mul hg, hz, meromorphicOrderAt_mul (hf z hz) (hg z hz), ← hm, ← hn,
      ← WithTop.coe_add]
  · simp [hz]

/-- On a preperfect set, the divisor of the inverse is the negative of the divisor. -/
theorem divisor_inv (hU : Preperfect U) (a : functionRing 𝕜 𝕜' U) : divisor a⁻¹ = -divisor a := by
  rw [divisor_coe hU (meromorphicOn_out a).inv (by rw [Germ.coe_inv, coe_out, coe_inv])]
  ext z
  by_cases hz : z ∈ U
  · simp [divisor, meromorphicOn_out a, (meromorphicOn_out a).inv, hz, meromorphicOrderAt_inv]
  · simp [hz]

/-!
## The Normal Form Representative
-/

/-- The canonical representative of an element of `functionRing 𝕜 𝕜' U`: the normal form of the
chosen representative. On open sets, this is the unique representative in normal form, up to
values outside of `U`, see `MeromorphicOn.FunctionRing.eqOn_toNF_of_meromorphicNFOn`.

Since functions in normal form are not stable under addition or multiplication, `toNF` is a
section of `MeromorphicOn.toFunctionRingAlgHom` as a map of sets, not an algebra homomorphism. -/
noncomputable def toNF (a : functionRing 𝕜 𝕜' U) : 𝕜 → 𝕜' := toMeromorphicNFOn (out a) U

/-- The canonical representative is in normal form. -/
theorem meromorphicNFOn_toNF (a : functionRing 𝕜 𝕜' U) : MeromorphicNFOn (toNF a) U :=
  meromorphicNFOn_toMeromorphicNFOn (out a) U

/-- The canonical representative represents the element. -/
@[simp]
theorem coe_toNF (a : functionRing 𝕜 𝕜' U) :
    ((toNF a : 𝕜 → 𝕜') : Germ (codiscreteWithin U) 𝕜') = a := by
  rw [← coe_out a]
  exact (Germ.coe_eq.2 (toMeromorphicNFOn_eqOn_codiscrete (meromorphicOn_out a))).symm

/-- The map `toNF` is a section of the quotient map `toFunctionRingAlgHom`. -/
theorem toFunctionRingAlgHom_toNF (a : functionRing 𝕜 𝕜' U) :
    toFunctionRingAlgHom ⟨toNF a, (meromorphicNFOn_toNF a).meromorphicOn⟩ = a :=
  Subtype.ext (coe_toNF a)

/-- On open sets, any normal-form representative of an element agrees with the canonical
representative on `U`. Off `U`, representatives of the element are unconstrained, so this is the
strongest possible uniqueness statement. -/
theorem eqOn_toNF_of_meromorphicNFOn (hU : IsOpen U) {a : functionRing 𝕜 𝕜' U}
    (h₁g : MeromorphicNFOn g U) (h₂g : (g : Germ (codiscreteWithin U) 𝕜') = a) :
    Set.EqOn g (toNF a) U := by
  intro x hx
  have h₁ : g =ᶠ[codiscreteWithin U] toNF a := Germ.coe_eq.1 (by rw [h₂g, coe_toNF])
  have h₂ : g =ᶠ[𝓝[≠] x] toNF a :=
    (eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE hU).1 h₁ x hx
  have h₃ : g =ᶠ[𝓝 x] toNF a :=
    ((h₁g hx).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (meromorphicNFOn_toNF a hx)).1 h₂
  exact h₃.eq_of_nhds

end MeromorphicOn.FunctionRing

/-!
## The Global Case

For `U = univ`, the ring `MeromorphicOn.functionRing 𝕜 𝕜' univ` is the ring of meromorphic
functions on `𝕜`. The following `Fact` instances make it a field whenever `𝕜` is preconnected, for
instance if `𝕜` is `ℝ` or `ℂ`. Over totally disconnected fields such as the `p`-adic numbers, it is
not a field.
-/

instance [PreconnectedSpace 𝕜] : Fact (IsPreconnected (univ : Set 𝕜)) :=
  ⟨isPreconnected_univ⟩

instance : Fact (univ : Set 𝕜).Nontrivial :=
  ⟨nontrivial_univ⟩

theorem MeromorphicOn.mem_subalgebra_univ_iff :
    f ∈ MeromorphicOn.subalgebra 𝕜 𝕜' univ ↔ Meromorphic f :=
  meromorphicOn_univ

/-- The chosen representative of an element of `functionRing 𝕜 𝕜' univ` is meromorphic. -/
theorem MeromorphicOn.FunctionRing.meromorphic_out (a : functionRing 𝕜 𝕜' univ) :
    Meromorphic (out a) :=
  meromorphicOn_univ.1 (meromorphicOn_out a)

namespace Meromorphic

open MeromorphicOn

/-- The germ of a meromorphic function lies in `functionRing 𝕜 𝕜' univ`. -/
theorem coe_mem_functionRing (hf : Meromorphic f) :
    (f : Germ (codiscreteWithin (univ : Set 𝕜)) 𝕜') ∈ functionRing 𝕜 𝕜' univ :=
  MeromorphicOn.coe_mem_functionRing hf.meromorphicOn

/-- The element of `functionRing 𝕜 𝕜' univ` represented by a meromorphic function. -/
def toFunctionRing (hf : Meromorphic f) : functionRing 𝕜 𝕜' univ :=
  FunctionRing.mk hf.meromorphicOn

@[simp]
theorem coe_toFunctionRing (hf : Meromorphic f) :
    ((hf.toFunctionRing : functionRing 𝕜 𝕜' univ) : Germ (codiscreteWithin (univ : Set 𝕜)) 𝕜') =
      f :=
  rfl

/-- A meromorphic function agrees with the chosen representative of the element it represents,
away from a discrete set. -/
theorem eventuallyEq_out_toFunctionRing (hf : Meromorphic f) :
    f =ᶠ[codiscrete 𝕜] FunctionRing.out hf.toFunctionRing :=
  FunctionRing.eventuallyEq_out_mk hf.meromorphicOn

end Meromorphic
