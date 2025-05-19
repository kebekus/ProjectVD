import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Meromorphic.FactorizedRational
import VD.ToMathlib.LeadCoefficient
import VD.IsolatedZeros

open Classical Function Function.FactorizedRational MeromorphicAt MeromorphicOn Real Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Theorems concerning the Leading Coefficient
-/

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
    rw [Finset.prod_insert hσ, Finset.prod_insert hσ, leadCoefficient_mul (h σ) (MeromorphicAt.prod h),
      hind]

/-!
## Theorems concerning Affine Functions
-/

theorem meromorphicAt_affine (y x : 𝕜) :
    MeromorphicAt (· - y) x := by fun_prop

theorem MeromorphicAt.order_affine {x y : 𝕜} :
    (meromorphicAt_affine y x).order ≠ ⊤ := by
  rw [MeromorphicAt.order_ne_top_iff₂]
  apply mem_nhdsWithin.2
  by_cases h : x = y
  · use Set.univ
    simp only [isOpen_univ, Set.mem_univ, Set.univ_inter, ne_eq, true_and, h]
    intro z hz
    simp_all [sub_eq_zero]
  · use {y}ᶜ
    simp_all only [isOpen_compl_iff, Set.finite_singleton, Set.Finite.isClosed, Set.mem_compl_iff,
      Set.mem_singleton_iff, not_false_eq_true, ne_eq, true_and]
    intro z hz
    simp_all [sub_eq_zero]

theorem leadCoefficient_affine {x y : 𝕜} :
    leadCoefficient (· - y) x = if x = y then 1 else x - y := by
  by_cases h : x = y
  · simp_all only [sub_self, ite_true]
    apply AnalyticAt.leadCoefficient_of_order_eq_finite₁ (n := 1) (by fun_prop) (by apply one_ne_zero)
    simp_all
  · simp_all only [ite_false]
    apply AnalyticAt.leadCoefficient_of_nonvanish (by fun_prop)
    simp_all [sub_ne_zero]

/-!
## Theorems concerning Factorized Rational Functions
-/

private lemma Function.FactorizedRational.mulSupport_update {d : 𝕜 → ℤ} {x : 𝕜}
    (h : d.support.Finite) :
    (fun u ↦ (x - u) ^ Function.update d x 0 u).mulSupport ⊆ h.toFinset := by
  intro u
  contrapose
  simp only [mem_mulSupport, ne_eq, Decidable.not_not]
  by_cases h₁ : u = x
  · rw [h₁]
    simp
  · simp_all

theorem Function.FactorizedRational.leadCoefficient {d : 𝕜 → ℤ} {x : 𝕜} (h : d.support.Finite) :
    leadCoefficient (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ update d x 0 u := by
  have : (fun u ↦ (· - u) ^ d u).mulSupport ⊆ h.toFinset := by
    simp [Function.FactorizedRational.mulSupport]
  rw [finprod_eq_prod_of_mulSupport_subset _ this, leadCoefficient_prod (fun _ ↦ by fun_prop),
    finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h)]
  apply Finset.prod_congr rfl
  intro y hy
  rw [leadCoefficient_zpow₁ (by fun_prop) (by simp [MeromorphicAt.order_affine])]
  by_cases hxy : x = y
  · rw [hxy, leadCoefficient_affine]
    simp_all
  · rw [leadCoefficient_affine]
    simp only [hxy, reduceIte]
    congr
    apply (Function.update_of_ne (by tauto) _ _).symm

theorem Function.FactorizedRational.leadCoefficient_off_support {d : 𝕜 → ℤ} {x : 𝕜}
    (h₁ : d.support.Finite) (h₂ : x ∉ d.support) :
    MeromorphicAt.leadCoefficient (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ d u := by
  rw [leadCoefficient h₁, finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h₁)]
  have : (fun u ↦ (x - u) ^ d u).mulSupport ⊆ h₁.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finprod_eq_prod_of_mulSupport_subset _ this, Finset.prod_congr rfl]
  intro y hy
  congr
  apply Function.update_of_ne
  by_contra hCon
  simp_all

theorem log_norm_leadCoefficient {d : 𝕜 → ℤ} {x : 𝕜} (h : d.support.Finite) :
    log ‖leadCoefficient (∏ᶠ u, (· - u) ^ d u) x‖ = ∑ᶠ u, (d u) * log ‖x - u‖ := by
  -- Simplify left side
  rw [leadCoefficient h, finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h)]
  have : ∀ y ∈ h.toFinset, ‖(x - y) ^ update d x 0 y‖ ≠ 0 := by
    intro y _
    by_cases h : x = y
    · rw [h]
      simp_all
    · simp_all [update_of_ne (by tauto), zpow_ne_zero, sub_ne_zero]
  rw [norm_prod, log_prod _ _ this]
  -- Simplify right side
  have : (fun u ↦ (d u) * log ‖x - u‖).support ⊆ h.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finsum_eq_sum_of_support_subset _ this]
  -- Prove equality summand by summand
  apply Finset.sum_congr rfl
  intro y hy
  rw [norm_zpow, Real.log_zpow]
  by_cases h : x = y
  · simp [h]
  · rw [Function.update_of_ne (by tauto)]

/-!
# Special Terms in Elimination
-/

theorem MeromorphicOn.extract_zeros_poles_leadCoefficient
    {U : Set 𝕜} {x : 𝕜} {f g : 𝕜 → E}
    {D : Function.locallyFinsuppWithin U ℤ}
    (hD : D.support.Finite)
    (h₁x : x ∈ U)
    (h₂x : Uᶜ ∉ 𝓝[≠] x)
    (h₁f : MeromorphicAt f x)
    (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0)
    (h₃g : f =ᶠ[Filter.codiscreteWithin U] (∏ᶠ u, (· - u) ^ D u) • g) :
    leadCoefficient f x = (∏ᶠ u, (x - u) ^ update D x 0 u) • g x := by
  have t₀ : MeromorphicAt (∏ᶠ u, (· - u) ^ D u) x :=
    (FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x
  rw [leadCoefficient_congr_nhdNE
    (h₁f.eventuallyEq_nhdNE_of_eventuallyEq_codiscreteWithin (by fun_prop) h₁x h₂x h₃g),
    t₀.leadCoefficient_smul h₁g.meromorphicAt,
    h₁g.leadCoefficient_of_nonvanish h₂g]
  simp [Function.FactorizedRational.leadCoefficient hD]

theorem MeromorphicOn.extract_zeros_poles_leadCoefficient_log_norm
    {U : Set 𝕜} {x : 𝕜} {f g : 𝕜 → E}
    {D : Function.locallyFinsuppWithin U ℤ}
    (hD : D.support.Finite)
    (h₁x : x ∈ U)
    (h₂x : Uᶜ ∉ 𝓝[≠] x)
    (h₁f : MeromorphicAt f x)
    (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0)
    (h₃g : f =ᶠ[Filter.codiscreteWithin U] (∏ᶠ u, (· - u) ^ D u) • g) :
    log ‖leadCoefficient f x‖ = ∑ᶠ u, (D u) * log ‖x - u‖ + log ‖g x‖ := by
  have t₀ : MeromorphicAt ((∏ᶠ u, (· - u) ^ D u) • g) x := by
    apply MeromorphicAt.smul
    apply (FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x
    apply h₁g.meromorphicAt
  have t₁ := MeromorphicAt.eventuallyEq_nhdNE_of_eventuallyEq_codiscreteWithin
    h₁f t₀ h₁x h₂x h₃g
  rw [leadCoefficient_congr_nhdNE t₁,
    ((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x).leadCoefficient_smul
    h₁g.meromorphicAt]
  rw [h₁g.leadCoefficient_of_nonvanish h₂g]
  rw [norm_smul]
  rw [log_mul]
  congr
  apply log_norm_leadCoefficient hD
  --
  simp
  rw [eq_comm]
  apply ((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x).zero_ne_leadCoefficient
  apply FactorizedRational.order_ne_top
  --
  simp_all
