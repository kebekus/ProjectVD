/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Factorized Rational Functions

This file discusses functions `𝕜 → 𝕜` of the form `∏ᶠ u, (· - u) ^ d u`, where
`d : 𝕜 → ℤ` is integer-valued. We show that these "factorized rational
functions" are meromorphic in normal form, with divisor equal to `d`.

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
Helper Lemma: Identify the support of `d` as the mulsupport of the product
defining the factorized rational function.
-/
lemma Function.FactorizedRational.mulSupport (d : 𝕜 → ℤ) :
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
  · rw [← Function.FactorizedRational.mulSupport d] at h₁
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
  · rw [← Function.FactorizedRational.mulSupport d] at h₁
    rw [finprod_of_infinite_mulSupport h₁]
    apply analyticAt_const

lemma Function.FactorizedRational.zeroAt {d : 𝕜 → ℤ} {x : 𝕜} (h : d x = 0) :
    (∏ᶠ u, (· - u) ^ d u) x ≠ 0 := by
  by_cases h₁ : Set.Finite d.support
  · rw [← Function.FactorizedRational.mulSupport d] at h₁
    rw [finprod_eq_prod _ h₁]
    rw [Finset.prod_apply]
    rw [Finset.prod_ne_zero_iff]
    intro z hz
    simp only [Pi.pow_apply, ne_eq]
    by_cases h₂ : z = x
    · simp_all
    · apply zpow_ne_zero
      rw [sub_ne_zero]
      tauto
  · rw [← Function.FactorizedRational.mulSupport d] at h₁
    rw [finprod_of_infinite_mulSupport h₁]
    simp

open Classical in
lemma Function.FactorizedRational.analyticAt' {d : 𝕜 → ℤ} (u₀ : 𝕜) (hd : d.support.Finite) :
    (∏ᶠ u, (· - u) ^ d u) = ((· - u₀) ^ d u₀) * (∏ᶠ u, (· - u) ^ (update d u₀ 0 u)) := by
  by_cases h₁d : d u₀ = 0
  · rw [← eq_update_self_iff.2 h₁d]
    simp [h₁d]
  have t₀ : (mulSupport fun u ↦ (fun x ↦ x - u) ^ d u) ⊆ hd.toFinset := by
    simp [Function.FactorizedRational.mulSupport]
  rw [finprod_eq_prod_of_mulSupport_subset _ t₀]
  have t₁ : u₀ ∈ hd.toFinset := by
    simp_all
  rw [← Finset.mul_prod_erase hd.toFinset _ t₁]
  congr 1
  have t₂ : (mulSupport fun u ↦ (fun x ↦ x - u) ^ (update d u₀ 0 u)) ⊆ hd.toFinset.erase u₀ := by
    rw [Function.FactorizedRational.mulSupport]
    intro x hx
    by_cases h₁x : x = u₀ <;> simp_all
  rw [finprod_eq_prod_of_mulSupport_subset _ t₂]
  apply Finset.prod_congr rfl
  intro x hx
  rw [eq_comm]
  simp_all

/-- Laurent polynomials are meromorphic in normal form on `⊤`. -/
theorem meromorphicNFOn_laurentPolynomial_top (d : 𝕜 → ℤ) :
    MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) ⊤ := by
  classical
  by_cases hd : d.support.Finite
  · intro z hz
    rw [Function.FactorizedRational.analyticAt' z hd]
    right
    use d z, (∏ᶠ u, (· - u) ^ update d z 0 u)
    constructor
    · simp [Function.FactorizedRational.analyticAt]
    · constructor
      · apply FactorizedRational.zeroAt
        simp
      · simp
  · rw [← Function.FactorizedRational.mulSupport d] at hd
    rw [finprod_of_infinite_mulSupport hd]
    apply AnalyticOnNhd.meromorphicNFOn
    apply analyticOnNhd_const


/-- Laurent polynomials are meromorphic in normal form on arbitrary subsets of `𝕜`. -/
theorem meromorphicNFOn_laurentPolynomial (d : 𝕜 → ℤ) (U : Set 𝕜) :
    MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) U := by
  intro z hz
  exact meromorphicNFOn_laurentPolynomial_top d (trivial)

/-- The order of the Laurent polynomial `(∏ᶠ u, fun z ↦ (z - u) ^ d u)` at z equals `d z`. -/
theorem order_laurentPolynomial {z : 𝕜} (d : 𝕜 → ℤ) (h₁d : Set.Finite d.support) :
    (((meromorphicNFOn_laurentPolynomial_top d).meromorphicOn) z trivial).order = d z := by
  classical
  rw [MeromorphicAt.order_eq_int_iff]
  use (∏ᶠ u, (· - u) ^ update d z 0 u)
  constructor
  · simp [Function.FactorizedRational.analyticAt]
  · constructor
    · apply FactorizedRational.zeroAt
      simp
    · filter_upwards
      rw [Function.FactorizedRational.analyticAt' z h₁d]
      intro a
      simp

/--
Laurent polynomials are nowhere locally constant zero.
-/
theorem order_LaurentPolynomial_ne_top {z : 𝕜} (d : 𝕜 → ℤ) :
    (meromorphicNFOn_laurentPolynomial_top d (trivial : z ∈ ⊤)).meromorphicAt.order ≠ ⊤ := by
  by_cases hd : Set.Finite (Function.support d)
  · simp [order_laurentPolynomial d hd]
  · rw [← Function.FactorizedRational.mulSupport] at hd
    have : AnalyticAt 𝕜 (1 : 𝕜 → 𝕜) z := analyticAt_const
    simp [finprod_of_infinite_mulSupport hd, this.meromorphicAt_order,
      this.order_eq_zero_iff.2 (by simp)]

/--
If `D` is a divisor, then the function associated with the divisor of the Laurent polynomial equals
`D`.
-/
theorem divisor_laurentPolynomial_within [CompleteSpace 𝕜] {U : Set 𝕜}
    (D : Function.locallyFinsuppWithin U ℤ) (hD : Set.Finite D.support) :
    MeromorphicOn.divisor (∏ᶠ u, (· - u) ^ D u) U = D := by
  ext z
  by_cases hz : z ∈ U
  · simp [(meromorphicNFOn_laurentPolynomial D U).meromorphicOn, hz,
      MeromorphicOn.divisor_apply, order_laurentPolynomial D hD]
  · simp [hz]
