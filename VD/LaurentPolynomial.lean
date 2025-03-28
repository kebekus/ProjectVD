/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Meromorphic.Divisor
import VD.ToMathlib.NormalForm
import VD.ToMathlib.Congruence_Divisor


-- -----------------
variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {U : Set 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
Conversion to normal form on `U` does not affect the divisor.
-/
theorem divisor_toMeromorphicNFOn [CompleteSpace E] {f : 𝕜 → E} (hf : MeromorphicOn f U) :
    MeromorphicOn.divisor f U = MeromorphicOn.divisor (toMeromorphicNFOn f U) U := by
  rw [← hf.divisor_congr_codiscreteWithin (toMeromorphicNFOn_eqOn_codiscrete hf)]
  exact toMeromorphicNFOn_eq_self_on_compl hf

-- -----------------

/--
Any set is codiscrete within itself.
-/
theorem Filter.codiscreteWithin_self {X : Type*} [TopologicalSpace X] (U : Set X) :
    U ∈ Filter.codiscreteWithin U := by simp [mem_codiscreteWithin]

-- -----------------

/--
If `X` is a `T1Space`, then functions with locally finite support within `U`
have discrete support within `U`.
-/
theorem Function.locallyFinsuppWithin.supportDiscreteWithinDomain
    {X : Type*} [TopologicalSpace X] [T1Space X] (U : Set X)
    {Y : Type*} [Zero Y]
    (f : Function.locallyFinsuppWithin U Y) :
    f =ᶠ[Filter.codiscreteWithin U] 0 := by
  apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
  have : f.support = (U \ {x | f x = (0 : X → Y) x}) := by
    ext x
    simp only [mem_support, ne_eq, Pi.zero_apply, Set.mem_diff, Set.mem_setOf_eq, iff_and_self]
    exact (support_subset_iff.1 f.supportWithinDomain) x
  rw [← this]
  exact f.supportLocallyFiniteWithinDomain

-- -----------------

/-!
# Laurent polynomials

This file discusses Laurent polynomials as examples of meromorphic functions in
normal form. Laurent polynomials are functions on a non-trivially normed field
`𝕜` of the form `(∏ᶠ u, fun z ↦ (z - u) ^ d u)`, where `d : 𝕜 → ℤ` has finite
support. We show that Laurent polynomials are meromorphic in normal form, with
divisor equal to `d`.
-/

open Classical Real Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {U : Set 𝕜}
  {z : 𝕜}

private lemma analyticAt_finLaurentPolynomial_off_support (d : 𝕜 → ℤ) (P : Finset 𝕜)
    (hz : z ∉ P) :
    AnalyticAt 𝕜 (∏ u ∈ P, fun z ↦ (z - u) ^ d u) z := by
  rw [Finset.prod_fn]
  apply Finset.analyticAt_prod
  intro u hu
  apply AnalyticAt.zpow
  fun_prop
  rw [sub_ne_zero, ne_comm]
  exact ne_of_mem_of_not_mem hu hz

/-- Laurent polynomials are meromorphic in normal form on `⊤`. -/
theorem meromorphicNF_LaurentPolynomial (d : 𝕜 → ℤ) :
    MeromorphicNFOn (∏ᶠ u, fun z ↦ (z - u) ^ d u) ⊤ := by
  by_cases hd : (Function.mulSupport fun u z => (z - u) ^ d u).Finite
  · rw [finprod_eq_prod _ hd]
    intro z hz
    by_cases h₂z : z ∈ hd.toFinset
    · rw [← Finset.mul_prod_erase hd.toFinset _ h₂z]
      right
      use d z, ∏ x ∈ hd.toFinset.erase z, fun z => (z - x) ^ d x,
        analyticAt_finLaurentPolynomial_off_support d (hd.toFinset.erase z)
          (Finset.not_mem_erase z hd.toFinset)
      constructor
      · rw [Finset.prod_apply, Finset.prod_ne_zero_iff]
        intro u hu
        apply zpow_ne_zero
        rw [sub_ne_zero]
        by_contra hCon
        rw [hCon] at hu
        have := Finset.not_mem_erase u hd.toFinset
        tauto
      · exact Filter.Eventually.of_forall (congrFun rfl)
    · exact (analyticAt_finLaurentPolynomial_off_support d hd.toFinset h₂z).meromorphicNFAt
  · rw [finprod_of_infinite_mulSupport hd]
    apply analyticOnNhd_const.meromorphicNFOn

/-- Laurent polynomials are meromorphic in normal form on arbitrary subsets of `𝕜`. -/
theorem MeromorphicNFOn_LaurentPolynomial (d : 𝕜 → ℤ) (U : Set 𝕜) :
    MeromorphicNFOn (∏ᶠ u, fun z ↦ (z - u) ^ d u) U := by
  intro z hz
  exact meromorphicNF_LaurentPolynomial d z (trivial)

/--
Helper Lemma: Identifying the support of `d` as the mulsupport of the product
defining the Laurent polynomial.
-/
lemma mulsupport_LaurentPolynomial (d : 𝕜 → ℤ) :
    (Function.mulSupport fun u z ↦ (z - u) ^ d u) = d.support := by
  ext u
  constructor
  · intro h
    simp_all only [Function.mem_mulSupport, ne_eq, Function.mem_support]
    by_contra hCon
    simp only [hCon, zpow_zero] at h
    tauto
  · intro h
    simp only [Function.mem_mulSupport, ne_eq]
    by_contra hCon
    have := congrFun hCon u
    simp only [sub_self, Pi.one_apply] at this
    have : (0 : 𝕜) ^ d u ≠ 0 := ne_zero_of_eq_one this
    rw [zpow_ne_zero_iff h] at this
    tauto

/-- The order of the Laurent polynomial `(∏ᶠ u, fun z ↦ (z - u) ^ d u)` at z equals `d z`. -/
theorem order_LaurentPolynomial {z : 𝕜} (d : 𝕜 → ℤ) (h₁d : Set.Finite d.support) :
    (((meromorphicNF_LaurentPolynomial d).meromorphicOn) z trivial).order = d z := by
  rw [MeromorphicAt.order_eq_int_iff]
  use ∏ x ∈ h₁d.toFinset.erase z, fun z => (z - x) ^ d x,
    analyticAt_finLaurentPolynomial_off_support d (h₁d.toFinset.erase z)
      (Finset.not_mem_erase z h₁d.toFinset)
  constructor
  · simp only [Finset.prod_apply]
    rw [Finset.prod_ne_zero_iff]
    intro u hu
    apply zpow_ne_zero
    rw [sub_ne_zero]
    by_contra hCon
    rw [hCon] at hu
    have := Finset.not_mem_erase u h₁d.toFinset
    tauto
  · apply Filter.Eventually.of_forall
    intro x
    have t₀ : (Function.mulSupport fun u z => (z - u) ^ d u).Finite := by
      rwa [mulsupport_LaurentPolynomial d]
    have t₁ : h₁d.toFinset = t₀.toFinset := by
      simp [eq_comm, mulsupport_LaurentPolynomial d]
    rw [finprod_eq_prod _ t₀, t₁, eq_comm]
    simp only [Finset.prod_apply, smul_eq_mul]
    have : z ∉ h₁d.toFinset.erase z := Finset.not_mem_erase z h₁d.toFinset
    by_cases hz : z ∈ h₁d.toFinset
    · rw [t₁] at hz
      simp_rw [← Finset.mul_prod_erase t₀.toFinset _ hz]
    · have : t₀.toFinset = t₀.toFinset.erase z := by
        rw [eq_comm]
        apply Finset.erase_eq_of_not_mem
        rwa [t₁] at hz
      rw [this]
      have : (x - z) ^ d z = 1 := by
        simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Decidable.not_not] at hz
        simp [hz]
      rw [this]
      simp

/--
Laurent polynomials are nowhere locally constant zero.
-/
theorem order_LaurentPolynomial_ne_top {z : 𝕜} (d : 𝕜 → ℤ) :
    ((meromorphicNF_LaurentPolynomial d) z trivial).meromorphicAt.order ≠ ⊤ := by
  by_cases hd : Set.Finite (Function.support d)
  · simp [order_LaurentPolynomial d hd]
  · rw [← mulsupport_LaurentPolynomial] at hd
    have : AnalyticAt 𝕜 (1 : 𝕜 → 𝕜) z := analyticAt_const
    simp [finprod_of_infinite_mulSupport hd, this.meromorphicAt_order,
      this.order_eq_zero_iff.2 (by simp)]

/--
The divisor function associated with the divisor of the Laurent polynomial
`(∏ᶠ u, fun z ↦ (z - u) ^ d u)` equals `d`.
-/
theorem divisor_LaurentPolynomial [CompleteSpace 𝕜] (d : 𝕜 → ℤ)
  (h₁d : Set.Finite d.support) :
  MeromorphicOn.divisor (∏ᶠ u, fun z ↦ (z - u) ^ d u) ⊤ = d := by
  ext z
  simp_rw [MeromorphicOn.divisor_apply (meromorphicNF_LaurentPolynomial d).meromorphicOn
    (by simp : z ∈ Set.univ)]
  rw [order_LaurentPolynomial d h₁d]
  simp

/--
If `D` is a divisor, then the function associated with the divisor of the
Laurent polynomial equals `D`.
-/
theorem divisor_LaurentPolynomial_within [CompleteSpace 𝕜] {U : Set 𝕜}
    (D : Function.locallyFinsuppWithin U ℤ) (hD : Set.Finite D.support) :
    MeromorphicOn.divisor (∏ᶠ u, fun z ↦ (z - u) ^ D u) U = D := by
  ext z
  by_cases hz : z ∈ U
  · simp [(MeromorphicNFOn_LaurentPolynomial D U).meromorphicOn, hz,
      MeromorphicOn.divisor_apply, order_LaurentPolynomial D hD]
  · simp [hz]

/-!
## Extration of Zeros and Poles
-/

/--
If `f` is meromorphic on an open set `U`, if `f` is nowhere locally constant
zero, and if the support of the divisor of `f` is finite, then there exists an
analytic function `g` on `U` without zeros such that `f` is the product of the
Laurent polynomial associated with the divisor of `f` and `g`.
-/
theorem MeromorphicOn.extract_zeros_poles [CompleteSpace 𝕜] {f : 𝕜 → E}
    (h₁f : MeromorphicOn f U) (h₂f : ∀ u : U, (h₁f u u.2).order ≠ ⊤)
    (h₃f : (divisor f U).support.Finite) :
    ∃ g : 𝕜 → E, AnalyticOnNhd 𝕜 g U ∧ (∀ u : U, g u ≠ 0) ∧
      f =ᶠ[Filter.codiscreteWithin U] (∏ᶠ u, fun z ↦ (z - u) ^ ((divisor f U) u)) • g := by
  -- Take `g` as the inverse of the Laurent polynomial defined below, converted
  -- to a meromorphic function in normal form. Then check all the properties.
  let φ := ∏ᶠ u, fun z ↦ (z - u) ^ (divisor f U u)
  have hφ : MeromorphicOn φ U :=
    (meromorphicNF_LaurentPolynomial (divisor f U)).meromorphicOn.mono_set (by tauto)
  let g := toMeromorphicNFOn (φ⁻¹ • f) U
  have hg : MeromorphicNFOn g U := by apply meromorphicNFOn_toMeromorphicNFOn
  refine ⟨g, ?_, ?_, ?_⟩
  · -- AnalyticOnNhd 𝕜 g U
    rw [← hg.nonneg_divisor_iff_analyticOnNhd, ← divisor_toMeromorphicNFOn (hφ.inv.smul h₁f),
      divisor_smul hφ.inv h₁f _ (fun z hz ↦ h₂f ⟨z, hz⟩), divisor_inv,
      divisor_LaurentPolynomial_within _ h₃f, neg_add_cancel]
    intro z hz
    simp [(hφ z hz).order_inv, order_LaurentPolynomial_ne_top (divisor f U)]
  · -- ∀ (u : ↑U), g ↑u ≠ 0
    intro ⟨u, hu⟩
    rw [← (hg u hu).order_eq_zero_iff, ← ((hφ.inv.smul h₁f) u hu).order_congr
      (toMeromorphicNFOn_eq_self_on_nhdNE (hφ.inv.smul h₁f) hu).symm]
    rw [(hφ u hu).inv.order_smul (h₁f u hu), (hφ u hu).order_inv, order_LaurentPolynomial _ h₃f]
    simp only [Pi.neg_apply, h₁f, hu, divisor_apply, WithTop.LinearOrderedAddCommGroup.coe_neg]
    lift (h₁f u hu).order to ℤ using (h₂f ⟨u, hu⟩) with n hn
    rw [WithTop.untop₀_coe, (by rfl : -↑(n : WithTop ℤ) = (↑(-n) : WithTop ℤ)), ← WithTop.coe_add]
    simp
  · -- f =ᶠ[Filter.codiscreteWithin U] (∏ᶠ (u : 𝕜), fun z ↦ (z - u) ^ (divisor f U) u) * g
    filter_upwards [(divisor f U).supportDiscreteWithinDomain,
      (hφ.inv.smul h₁f).meromorphicNFAt_mem_codiscreteWithin,
      Filter.codiscreteWithin_self U] with a h₂a h₃a h₄a
    unfold g
    simp only [Pi.smul_apply', toMeromorphicNFOn_eq_toMeromorphicNFAt (hφ.inv.smul h₁f) h₄a,
      ← toMeromorphicNFAt_eq_self.1 h₃a, Pi.inv_apply]
    rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ _, one_smul]
    rwa [← ((meromorphicNF_LaurentPolynomial (divisor f U)) a trivial).order_eq_zero_iff,
      order_LaurentPolynomial, h₂a, Pi.zero_apply, WithTop.coe_zero]

/--
If `f` is meromorphic on an open set `U`, if `f` is nowhere locally constant
zero, and if the support of the divisor of `f` is finite, then there exists an
analytic function `g` on `U` without zeros such that `log ‖f‖` is equivalent,
modulo equality on codiscrete subsets of `U` to
`∑ᶠ u, (divisor f U u * log ‖z-u‖) + log ‖g z‖`.
-/
theorem MeromorphicOn.extract_zeros_poles_log [CompleteSpace 𝕜] {f : 𝕜 → E}
    (h₁f : MeromorphicOn f U) (h₂f : ∀ u : U, (h₁f u u.2).order ≠ ⊤)
    (h₃f : (divisor f U).support.Finite) :
    ∃ g : 𝕜 → E, AnalyticOnNhd 𝕜 g U ∧ (∀ u : U, g u ≠ 0) ∧
      (fun z ↦ log ‖f z‖) =ᶠ[Filter.codiscreteWithin U]
        fun z ↦ ∑ᶠ u, (divisor f U u * log ‖z-u‖) + log ‖g z‖ := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := MeromorphicOn.extract_zeros_poles h₁f h₂f h₃f
  use g, h₁g, h₂g
  filter_upwards [h₃g, (divisor f U).supportDiscreteWithinDomain,
    Filter.codiscreteWithin_self U] with z hz h₂z h₃z
  -- Identify finprod with prod over h₃f.toFinset
  have : (Function.mulSupport fun u z ↦ (z - u) ^ (divisor f U) u) ⊆ h₃f.toFinset := by
    intro u hu
    by_contra hCon
    simp_all only [ne_eq, Subtype.forall, Pi.smul_apply', divisor_apply, Pi.zero_apply,
      WithTop.untopD_eq_self_iff, WithTop.coe_zero, or_false, Function.mem_mulSupport,
      Set.Finite.coe_toFinset, Function.mem_support, Decidable.not_not, zpow_zero]
    tauto
  rw [hz, finprod_eq_prod_of_mulSupport_subset _ this]
  -- Identify finsum with sum over h₃f.toFinset
  have : (Function.support fun u ↦ ↑((divisor f U) u) * log ‖z - u‖) ⊆ h₃f.toFinset := by
    intro u hu
    simp_all
  rw [finsum_eq_sum_of_support_subset _ this]
  -- Decompose LHS of the equation
  have : ∀ x ∈ h₃f.toFinset, ‖z - x‖ ^ (divisor f U) x ≠ 0 := by
    intro x hx
    rw [Set.Finite.mem_toFinset, Function.mem_support, ne_eq] at hx
    rw [ne_eq, zpow_eq_zero_iff hx, norm_eq_zero]
    by_contra hCon
    rw [sub_eq_zero] at hCon
    rw [hCon] at h₂z
    tauto
  simp only [Pi.smul_apply', Finset.prod_apply, norm_smul, norm_prod, norm_zpow, hz]
  rw [log_mul (Finset.prod_ne_zero_iff.2 this) (by simp [h₂g ⟨z, h₃z⟩]), log_prod _ _ this]
  simp [log_zpow]
