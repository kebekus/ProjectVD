import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Meromorphic.FactorizedRational
import VD.ToMathlib.LeadCoefficient

open Function Function.FactorizedRational MeromorphicAt MeromorphicOn Real Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Theorems about the leading coefficient
-/

theorem meromorphicAt_prod  {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    MeromorphicAt (∏ n ∈ s, f n) x := by
  classical
  apply Finset.induction (motive := fun s ↦ MeromorphicAt (∏ n ∈ s , f n) x)
  · rw [Finset.prod_empty]
    exact analyticAt_const.meromorphicAt
  · intro σ s hσ hind
    rw [Finset.prod_insert hσ]
    exact (h σ).mul hind

theorem leadCoefficient_const {x : 𝕜} {e : 𝕜} :
    leadCoefficient (fun _ ↦ e) x = e := by
  by_cases he : e = 0
  · rw [he]
    apply analyticAt_const.meromorphicAt.leadCoefficient_of_order_eq_top
    rw [MeromorphicAt.order_eq_top_iff]
    simp
  · exact analyticAt_const.leadCoefficient_of_nonvanish he

theorem leadCoefficient_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    leadCoefficient (∏ n ∈ s, f n) x = ∏ n ∈ s, leadCoefficient (f n) x := by
  classical
  apply Finset.induction
    (motive := fun b' ↦ (leadCoefficient (∏ n ∈ b' , f n) x = ∏ n ∈ b', leadCoefficient (f n) x))
  · simp only [Finset.univ_eq_empty, Finset.prod_empty, forall_const]
    apply leadCoefficient_const
  · intro σ s₁ hσ hind
    rw [Finset.prod_insert hσ, Finset.prod_insert hσ, leadCoefficient_mul (h σ) (meromorphicAt_prod h),
      hind]

theorem Function.FactorizedRational.leadCoefficient {d : 𝕜 → ℤ} {x : 𝕜}
    (h₁ : d.support.Finite) (h₂ : x ∉ d.support) :
    leadCoefficient (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ d u := by
  have : (fun u ↦ (· - u) ^ d u).mulSupport ⊆ h₁.toFinset := by
    simp [mulSupport]
  rw [finprod_eq_prod_of_mulSupport_subset _ this, leadCoefficient_prod (fun _ ↦ by fun_prop)]
  have : (fun u ↦ (x - u) ^ d u).mulSupport ⊆ h₁.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finprod_eq_prod_of_mulSupport_subset _ this]
  apply Finset.prod_congr rfl
  intro y hy
  have : x ≠ y := by
    by_contra hCon
    simp_all
  have t₁ : MeromorphicAt (· - y) x := (analyticAt_id.fun_sub analyticAt_const).meromorphicAt
  have t₂ : t₁.order ≠ ⊤ := by
    rw [MeromorphicAt.order_ne_top_iff₂]
    apply mem_nhdsWithin.2
    use {y}ᶜ, isOpen_compl_singleton
    constructor
    · simp_all
    · intro z hz
      simp_all [sub_eq_zero]
  rw [leadCoefficient_zpow₁ (by fun_prop) t₂,
    AnalyticAt.leadCoefficient_of_nonvanish (by fun_prop)]
  simp_all [sub_eq_zero]

open Classical

theorem leadCoefficientx {d : 𝕜 → ℤ} {x : 𝕜} (h : d.support.Finite) :
    leadCoefficient (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ update d x 0 u := by
  have : (fun u ↦ (· - u) ^ d u).mulSupport ⊆ h.toFinset := by
    simp [Function.FactorizedRational.mulSupport]
  rw [finprod_eq_prod_of_mulSupport_subset _ this, leadCoefficient_prod (fun _ ↦ by fun_prop)]
  have : (fun u ↦ (x - u) ^ Function.update d x 0 u).mulSupport ⊆ h.toFinset := by
    intro u
    contrapose
    intro hu
    simp_all
    by_cases h₁ : u = x
    · rw [h₁]
      simp
    · simp_all
  rw [finprod_eq_prod_of_mulSupport_subset _ this]
  apply Finset.prod_congr rfl
  intro y hy
  have t₁ : MeromorphicAt (· - y) x := (analyticAt_id.fun_sub analyticAt_const).meromorphicAt
  by_cases hxy : x = y
  · have t₂ : t₁.order ≠ ⊤ := by
      rw [MeromorphicAt.order_ne_top_iff₂]
      apply mem_nhdsWithin.2
      use Set.univ
      simp
      rw [hxy]
      intro z hz
      simp_all [sub_eq_zero]
    rw [leadCoefficient_zpow₁ (by fun_prop) t₂, hxy]
    simp
    convert one_zpow (d y)
    apply AnalyticAt.leadCoefficient_of_order_eq_finite₁ (n := 1) (by fun_prop) (by apply one_ne_zero)
    simp
  have t₂ : t₁.order ≠ ⊤ := by
    rw [MeromorphicAt.order_ne_top_iff₂]
    apply mem_nhdsWithin.2
    use {y}ᶜ, isOpen_compl_singleton
    constructor
    · simp_all
    · intro z hz
      simp_all [sub_eq_zero]
  rw [leadCoefficient_zpow₁ (by fun_prop) t₂,
    AnalyticAt.leadCoefficient_of_nonvanish (by fun_prop)]
  simp_all [sub_eq_zero]
  have : Function.update d x 0 y = d y := by
    exact Function.update_of_ne (fun a ↦ hxy (_root_.id (Eq.symm a))) 0 d
  simp_all [sub_eq_zero]
  simp_all [sub_eq_zero]

theorem log_norm_leadCoefficient {d : 𝕜 → ℤ} {x : 𝕜} (h : d.support.Finite) :
    log ‖leadCoefficient (∏ᶠ u, (· - u) ^ d u) x‖ = ∑ᶠ u, (d u) * log ‖x - u‖ := by
  rw [leadCoefficientx h]
  have : (fun u ↦ (x - u) ^ update d x 0 u).mulSupport ⊆ h.toFinset := by
    intro u
    contrapose
    intro hu
    simp_all
    by_cases h₁ : u = x
    · rw [h₁]
      simp
    · simp_all
  rw [finprod_eq_prod_of_mulSupport_subset _ this]
  have : ∀ y ∈ h.toFinset, ‖(x - y) ^ update d x 0 y‖ ≠ 0 := by
    intro y hy
    simp_all
    by_cases h : x = y
    · rw [h]
      simp_all
    · simp_all [update_of_ne (by tauto), zpow_ne_zero, sub_ne_zero]
  rw [norm_prod, log_prod _ _ this]
  --
  have : (fun u ↦ (d u) * log ‖x - u‖).support ⊆ h.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finsum_eq_sum_of_support_subset _ this]
  --
  apply Finset.sum_congr rfl
  intro y hy
  rw [norm_zpow, Real.log_zpow]
  by_cases h : x = y
  · simp [h]
  · congr
    apply Function.update_of_ne
    tauto
