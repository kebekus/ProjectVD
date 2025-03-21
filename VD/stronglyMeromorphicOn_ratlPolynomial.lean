/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.stronglyMeromorphicOn

/-!
# Laurent polynomials

This file discusses Laurent polynomials as examples of meromorphic functions.
Laurent polynomials are functions on a non-trivially normed field `𝕜` of the form
`(∏ᶠ u, fun z ↦ (z - u) ^ d u)`, where `d : 𝕜 → ℤ` has finite support. We show that
Laurent polynomials are meromorphic in normal form, with divisor equal to `d`.
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
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

/-- Laurent polynomials are meromorphic in normal form on ⊤. -/
theorem meromorphicNF_LaurentPolynomial [DecidableEq 𝕜] (d : 𝕜 → ℤ) :
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

theorem MeromorphicNFOn_set_LaurentPolynomial [DecidableEq 𝕜] (d : 𝕜 → ℤ) (U : Set 𝕜) :
    MeromorphicNFOn (∏ᶠ u, fun z ↦ (z - u) ^ d u) U := by
  intro z hz
  exact meromorphicNF_LaurentPolynomial d z (trivial)

private lemma mulsupport_LaurentPolynomial (d : 𝕜 → ℤ) :
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
theorem order_LaurentPolynomial [DecidableEq 𝕜] {z : 𝕜} (d : 𝕜 → ℤ) (h₁d : Set.Finite d.support) :
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

/-- Laurent polynomials are nowhere locally constant zero. -/
theorem order_LaurentPolynomial_ne_top [DecidableEq 𝕜] {z : 𝕜} (d : 𝕜 → ℤ) :
    ((meromorphicNF_LaurentPolynomial d) z trivial).meromorphicAt.order ≠ ⊤ := by
  by_cases hd : Set.Finite (Function.support d)
  · simp [order_LaurentPolynomial d hd]
  · rw [← mulsupport_LaurentPolynomial] at hd
    have : AnalyticAt 𝕜 (1 : 𝕜 → 𝕜) z := analyticAt_const
    simp [finprod_of_infinite_mulSupport hd, this.meromorphicAt_order,
      this.order_eq_zero_iff.2 (by simp)]

/-- The function associated with the divisor of the Laurent polynomial
`(∏ᶠ u, fun z ↦ (z - u) ^ d u)` equals `d`. -/
theorem MeromorphicNFOn_divisor_ratlPolynomial [CompleteSpace 𝕜] [DecidableEq 𝕜] (d : 𝕜 → ℤ)
  (h₁d : Set.Finite d.support) :
  MeromorphicOn.divisor (∏ᶠ u, fun z ↦ (z - u) ^ d u) ⊤ = d := by
  ext z
  simp_rw [MeromorphicOn.divisor_apply (meromorphicNF_LaurentPolynomial d).meromorphicOn
    (by simp : z ∈ Set.univ)]
  rw [order_LaurentPolynomial d h₁d]
  simp

/-- If `D` is a divisor, then the function associated with the divisor of the Laurent polynomial
equals `D`. -/
theorem MeromorphicNFOn_divisor_ratlPolynomial_U [CompleteSpace 𝕜] [DecidableEq 𝕜] {U : Set 𝕜}
    (D : DivisorOn U) (hD : Set.Finite D.support) :
    MeromorphicOn.divisor (∏ᶠ u, fun z ↦ (z - u) ^ D u) U = D := by
  ext z
  by_cases hz : z ∈ U
  · simp [(MeromorphicNFOn_set_LaurentPolynomial D U).meromorphicOn, hz,
      MeromorphicOn.divisor_apply, order_LaurentPolynomial D hD]
  · simp [hz]

-- ##################### --

theorem X [CompleteSpace 𝕜] [DecidableEq 𝕜] {f : 𝕜 → 𝕜} (h₁f : MeromorphicOn f U)
    (h₂f : ∀ u : U, (h₁f u u.2).order ≠ ⊤) (h₃f : Set.Finite (MeromorphicOn.divisor f U).support) :
    ∃ g : 𝕜 → 𝕜, AnalyticOnNhd 𝕜 g U ∧ ∀ u : U, g u ≠ 0 ∧
      f =ᶠ[Filter.codiscreteWithin U] (∏ᶠ u, fun z ↦ (z - u) ^ ((MeromorphicOn.divisor f U) u)) * g := by
  let g' := (∏ᶠ u, fun z ↦ (z - u) ^ (MeromorphicOn.divisor f U u))⁻¹ * f
  have h₁g' : MeromorphicOn g' U := by
    apply MeromorphicOn.mul _ h₁f
    apply MeromorphicOn.mono_set (U := ⊤)
    apply MeromorphicOn.inv
    apply (meromorphicNF_LaurentPolynomial (MeromorphicOn.divisor f U)).meromorphicOn
    tauto
  have h₂g' : MeromorphicOn.divisor g' U = 0 := by
    rw [MeromorphicOn.divisor_mul]
    rw [MeromorphicOn.divisor_inv]
    rw [MeromorphicNFOn_divisor_ratlPolynomial_U]
    simp
    assumption
    apply MeromorphicOn.mono_set (U := ⊤)
    apply MeromorphicOn.inv
    apply (meromorphicNF_LaurentPolynomial (MeromorphicOn.divisor f U)).meromorphicOn
    tauto
    assumption
    intro z hz
    sorry
    assumption
  let g := toMeromorphicNFOn ((∏ᶠ u, fun z ↦ (z - u) ^ (-(MeromorphicOn.divisor f U) u)) * f) U
  have h₁g : MeromorphicOn g U := by

    sorry
  have h₂g : AnalyticOnNhd g U := by
    sorry
  use g

  sorry
