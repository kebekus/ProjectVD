import VD.stronglyMeromorphicOn
import VD.meromorphicOn
import VD.meromorphicOn_divisor
import VD.mathlibAddOn

open scoped Interval Topology


theorem analyticAt_ratlPolynomial₁
  {z : ℂ}
  (d : ℂ → ℤ)
  (P : Finset ℂ) :
  z ∉ P → AnalyticAt ℂ (∏ u ∈ P, fun z ↦ (z - u) ^ d u) z := by
  intro hz
  rw [Finset.prod_fn]
  apply Finset.analyticAt_prod
  intro u hu
  apply AnalyticAt.zpow
  fun_prop
  rw [sub_ne_zero, ne_comm]
  exact ne_of_mem_of_not_mem hu hz


theorem stronglyMeromorphicOn_ratlPolynomial₂
  (d : ℂ → ℤ)
  (P : Finset ℂ) :
  StronglyMeromorphicOn (∏ u ∈ P, fun z ↦ (z - u) ^ d u) ⊤ := by

  intro z hz
  by_cases h₂z : z ∈ P
  · rw [← Finset.mul_prod_erase P _ h₂z]
    right
    use d z
    use ∏ x ∈ P.erase z, fun z => (z - x) ^ d x
    constructor
    · have : z ∉ P.erase z := Finset.not_mem_erase z P
      apply analyticAt_ratlPolynomial₁ d (P.erase z) this
    · constructor
      · simp only [Finset.prod_apply]
        rw [Finset.prod_ne_zero_iff]
        intro u hu
        apply zpow_ne_zero
        rw [sub_ne_zero]
        by_contra hCon
        rw [hCon] at hu
        let A := Finset.not_mem_erase u P
        tauto
      · exact Filter.Eventually.of_forall (congrFun rfl)
  · apply AnalyticAt.MeromorphicNFAt
    exact analyticAt_ratlPolynomial₁ d P (z := z) h₂z


theorem stronglyMeromorphicOn_ratlPolynomial₃
  (d : ℂ → ℤ) :
  StronglyMeromorphicOn (∏ᶠ u, fun z ↦ (z - u) ^ d u) ⊤ := by
  by_cases hd : (Function.mulSupport fun u z => (z - u) ^ d u).Finite
  · rw [finprod_eq_prod _ hd]
    apply stronglyMeromorphicOn_ratlPolynomial₂ d hd.toFinset
  · rw [finprod_of_infinite_mulSupport hd]
    apply AnalyticOn.stronglyMeromorphicOn
    apply analyticOnNhd_const


theorem stronglyMeromorphicOn_ratlPolynomial₃U
  (d : ℂ → ℤ)
  (U : Set ℂ) :
  StronglyMeromorphicOn (∏ᶠ u, fun z ↦ (z - u) ^ d u) U := by
  intro z hz
  exact stronglyMeromorphicOn_ratlPolynomial₃ d z (trivial)


theorem ratlPoly_mulsupport
  (d : ℂ → ℤ) :
  (Function.mulSupport fun u z ↦ (z - u) ^ d u) = d.support := by
  ext u
  constructor
  · intro h
    simp at h
    simp
    by_contra hCon
    rw [hCon] at h
    simp at h
    tauto
  · intro h
    simp
    by_contra hCon
    let A := congrFun hCon u
    simp at A
    have t₁ : (0 : ℂ) ^ d u ≠ 0 := ne_zero_of_eq_one A
    rw [zpow_ne_zero_iff h] at t₁
    tauto


theorem stronglyMeromorphicOn_divisor_ratlPolynomial₁
  {z : ℂ}
  (d : ℂ → ℤ)
  (h₁d : Set.Finite d.support) :
  (((stronglyMeromorphicOn_ratlPolynomial₃ d).meromorphicOn) z trivial).order = d z := by

  rw [MeromorphicAt.order_eq_int_iff]
  use ∏ x ∈ h₁d.toFinset.erase z, fun z => (z - x) ^ d x
  constructor
  · have : z ∉ h₁d.toFinset.erase z := Finset.not_mem_erase z h₁d.toFinset
    apply analyticAt_ratlPolynomial₁ d (h₁d.toFinset.erase z) this
  · constructor
    · simp only [Finset.prod_apply]
      rw [Finset.prod_ne_zero_iff]
      intro u hu
      apply zpow_ne_zero
      rw [sub_ne_zero]
      by_contra hCon
      rw [hCon] at hu
      let A := Finset.not_mem_erase u h₁d.toFinset
      tauto
    · apply Filter.Eventually.of_forall
      intro x
      have t₀ : (Function.mulSupport fun u z => (z - u) ^ d u).Finite := by
        rwa [ratlPoly_mulsupport d]
      rw [finprod_eq_prod _ t₀]
      have t₁ : h₁d.toFinset = t₀.toFinset := by
        simp
        rw [eq_comm]
        exact ratlPoly_mulsupport d
      rw [t₁]
      simp
      rw [eq_comm]
      have : z ∉ h₁d.toFinset.erase z := Finset.not_mem_erase z h₁d.toFinset
      by_cases hz : z ∈ h₁d.toFinset
      · rw [t₁] at hz
        conv =>
          right
          rw [← Finset.mul_prod_erase t₀.toFinset _ hz]
      · have : t₀.toFinset = t₀.toFinset.erase z := by
          rw [eq_comm]
          apply Finset.erase_eq_of_not_mem
          rwa [t₁] at hz
        rw [this]

        have : (x - z) ^ d z = 1 := by
          simp at hz
          rw [hz]
          simp
        rw [this]
        simp


theorem stronglyMeromorphicOn_ratlPolynomial₃order
  {z : ℂ}
  (d : ℂ → ℤ) :
  ((stronglyMeromorphicOn_ratlPolynomial₃ d) z trivial).meromorphicAt.order ≠ ⊤ := by

  have h₂d : (Function.mulSupport fun u z ↦ (z - u) ^ d u) = d.support := by
    ext u
    constructor
    · intro h
      simp at h
      simp
      by_contra hCon
      rw [hCon] at h
      simp at h
      tauto
    · intro h
      simp
      by_contra hCon
      let A := congrFun hCon u
      simp at A
      have t₁ : (0 : ℂ) ^ d u ≠ 0 := ne_zero_of_eq_one A
      rw [zpow_ne_zero_iff h] at t₁
      tauto

  by_cases hd : Set.Finite (Function.support d)
  · rw [stronglyMeromorphicOn_divisor_ratlPolynomial₁ d hd]
    simp
  · rw [← h₂d] at hd
    have : (Function.mulSupport fun u z => (z - u) ^ d u).Infinite := by
      exact hd
    simp_rw [finprod_of_infinite_mulSupport this]
    have : AnalyticAt ℂ (1 : ℂ → ℂ) z := by exact analyticAt_const
    rw [AnalyticAt.meromorphicAt_order this]
    rw [this.order_eq_zero_iff.2 (by simp)]
    simp


theorem stronglyMeromorphicOn_divisor_ratlPolynomial
  (d : ℂ → ℤ)
  (h₁d : Set.Finite d.support) :
  (stronglyMeromorphicOn_ratlPolynomial₃ d).meromorphicOn.divisorOn = d := by
  ext z
  rw [MeromorphicOn.divisorOn_def]
  simp
  rw [stronglyMeromorphicOn_divisor_ratlPolynomial₁ d h₁d]
  simp


theorem stronglyMeromorphicOn_divisor_ratlPolynomial_U
  {U : Set ℂ}
  (d : ℂ → ℤ)
  (h₁d : Set.Finite d.support)
  (h₂d : d.support ⊆ U) :
  (stronglyMeromorphicOn_ratlPolynomial₃U d U).meromorphicOn.divisorOn = d := by
  ext z
  rw [MeromorphicOn.divisorOn_def]
  by_cases hz : z ∈ U
  · simp [hz]
    rw [stronglyMeromorphicOn_divisor_ratlPolynomial₁ d h₁d]
    simp
  · simp [hz]
    rw [eq_comm, ← Function.nmem_support]
    tauto
