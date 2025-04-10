/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Factorized Rational Functions

This file discusses functions `𝕜 → 𝕜` of the form
`(∏ᶠ u, fun z ↦ (z - u) ^ d u)`, where `d : 𝕜 → ℤ` has finite support.
We show that these factorized
rational functions are meromorphic in normal form, with divisor equal to `d`.

TODO: Show that every meromorphic functions on a compact set is equivalent,
modulo equality on codiscrete sets, the the product of a factorized rational
function and an analytic function without zeros.
-/

open Function

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {U : Set 𝕜}
  {z : 𝕜}

/--
Factorized rational functions on a non-trivially normed field `𝕜` are functions
of the form `∏ᶠ u, (· - u) ^ d u`.
-/
noncomputable abbrev Function.FactorizedRational (d : 𝕜 → ℤ) := ∏ᶠ u, (· - u) ^ d u

/--
Helper Lemma: Identify the support of `d` as the mulsupport of the product
defining the factorized rational function.
-/
lemma Function.mulSupport_factorizedRational (d : 𝕜 → ℤ) :
    (Function.mulSupport fun u ↦ (· - u) ^ d u) = d.support := by
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
    simp only [Pi.pow_apply, sub_self, Pi.ofNat_apply] at this
    have : (0 : 𝕜) ^ d u ≠ 0 := ne_zero_of_eq_one this
    rw [zpow_ne_zero_iff h] at this
    tauto

lemma Function.FactorizedRational.analyticAt {d : 𝕜 → ℤ} {x : 𝕜} (h : 0 ≤ d x) :
    AnalyticAt 𝕜 (∏ᶠ u, (· - u) ^ d u) x := by
  by_cases h₁ : Set.Finite d.support
  · rw [← Function.mulSupport_factorizedRational d] at h₁
    rw [finprod_eq_prod _ h₁]
    have : (∏ i ∈ h₁.toFinset, (fun x ↦ x - i) ^ d i) = (fun x ↦ ∏ i ∈ h₁.toFinset, (x - i) ^ d i) := by
      ext x
      simp
    rw [this]
    apply Finset.analyticAt_prod
    intro u hu
    by_cases h₂ : x = u
    · apply AnalyticAt.fun_zpow_nonneg
      fun_prop
      rwa [← h₂]
    · apply AnalyticAt.fun_zpow
      fun_prop
      rwa [sub_ne_zero]
  · rw [← Function.mulSupport_factorizedRational d] at h₁
    rw [finprod_of_infinite_mulSupport h₁]
    apply analyticAt_const

private lemma analyticAt_finLaurentPolynomial_off_support (d : 𝕜 → ℤ) (P : Finset 𝕜)
    (hz : z ∉ P) :
    AnalyticAt 𝕜 (∏ u ∈ P, fun z ↦ (z - u) ^ d u) z := by
  rw [Finset.prod_fn]
  apply Finset.analyticAt_prod
  intro u hu
  apply AnalyticAt.zpow (by fun_prop)
  rw [sub_ne_zero, ne_comm]
  exact ne_of_mem_of_not_mem hu hz

/-- Laurent polynomials are meromorphic in normal form on `⊤`. -/
theorem meromorphicNFOn_laurentPolynomial_top (d : 𝕜 → ℤ) :
    MeromorphicNFOn (Function.FactorizedRational d) ⊤ := by
  classical
  by_cases hd : (Function.mulSupport fun u => (· - u) ^ d u).Finite
  · rw [Function.FactorizedRational, finprod_eq_prod _ hd]
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
  · rw [Function.FactorizedRational, finprod_of_infinite_mulSupport hd]
    apply analyticOnNhd_const.meromorphicNFOn

/-- Laurent polynomials are meromorphic in normal form on arbitrary subsets of `𝕜`. -/
theorem meromorphicNFOn_laurentPolynomial (d : 𝕜 → ℤ) (U : Set 𝕜) :
    MeromorphicNFOn (Function.FactorizedRational d) U := by
  intro z hz
  exact meromorphicNFOn_laurentPolynomial_top d (trivial)

/-- The order of the Laurent polynomial `(∏ᶠ u, fun z ↦ (z - u) ^ d u)` at z equals `d z`. -/
theorem order_laurentPolynomial {z : 𝕜} (d : 𝕜 → ℤ) (h₁d : Set.Finite d.support) :
    (((meromorphicNFOn_laurentPolynomial_top d).meromorphicOn) z trivial).order = d z := by
  classical
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
    have t₀ : (Function.mulSupport fun u => (· - u) ^ d u).Finite := by
      rwa [Function.mulSupport_factorizedRational d]
    have t₁ : h₁d.toFinset = t₀.toFinset := by
      simp [eq_comm, Function.mulSupport_factorizedRational d]
    rw [Function.FactorizedRational, finprod_eq_prod _ t₀, t₁, eq_comm]
    simp only [Finset.prod_apply, smul_eq_mul]
    by_cases hz : z ∈ h₁d.toFinset
    · rw [t₁] at hz
      simp_rw [← Finset.mul_prod_erase t₀.toFinset _ hz]
      simp
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
    (meromorphicNFOn_laurentPolynomial_top d (trivial : z ∈ ⊤)).meromorphicAt.order ≠ ⊤ := by
  by_cases hd : Set.Finite (Function.support d)
  · simp [order_laurentPolynomial d hd]
  · rw [← Function.mulSupport_factorizedRational] at hd
    have : AnalyticAt 𝕜 (1 : 𝕜 → 𝕜) z := analyticAt_const
    simp [finprod_of_infinite_mulSupport hd, this.meromorphicAt_order,
      this.order_eq_zero_iff.2 (by simp)]

/--
The divisor function associated with the divisor of the Laurent polynomial
`(∏ᶠ u, fun z ↦ (z - u) ^ d u)` equals `d`.
-/
theorem divisor_LaurentPolynomial [CompleteSpace 𝕜] (d : 𝕜 → ℤ) (h₁d : Set.Finite d.support) :
    MeromorphicOn.divisor (Function.FactorizedRational d) ⊤ = d := by
  ext z
  simp_rw [(meromorphicNFOn_laurentPolynomial_top d).meromorphicOn.divisor_apply
    (by simp : z ∈ Set.univ)]
  rw [order_laurentPolynomial d h₁d]
  simp

/--
If `D` is a divisor, then the function associated with the divisor of the Laurent polynomial equals
`D`.
-/
theorem divisor_laurentPolynomial_within [CompleteSpace 𝕜] {U : Set 𝕜}
    (D : Function.locallyFinsuppWithin U ℤ) (hD : Set.Finite D.support) :
    MeromorphicOn.divisor (Function.FactorizedRational D) U = D := by
  ext z
  by_cases hz : z ∈ U
  · simp [(meromorphicNFOn_laurentPolynomial D U).meromorphicOn, hz,
      MeromorphicOn.divisor_apply, order_laurentPolynomial D hD]
  · simp [hz]
