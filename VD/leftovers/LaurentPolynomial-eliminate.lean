import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import VD.leftovers.LaurentPolynomial
import VD.ToMathlib.Congruence_Divisor

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {U : Set 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

open Real

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
    rw [← hg.divisor_nonneg_iff_analyticOnNhd, divisor_of_toMeromorphicNFOn (hφ.inv.smul h₁f),
      divisor_smul hφ.inv h₁f _ (fun z hz ↦ h₂f ⟨z, hz⟩), divisor_inv,
      divisor_LaurentPolynomial_within _ h₃f, neg_add_cancel]
    intro z hz
    simp [(hφ z hz).order_inv, order_LaurentPolynomial_ne_top (divisor f U)]
  · -- ∀ (u : ↑U), g ↑u ≠ 0
    intro ⟨u, hu⟩
    rw [← (hg hu).order_eq_zero_iff, ← ((hφ.inv.smul h₁f) u hu).order_congr
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
      toMeromorphicNFAt_eq_self.2 h₃a, Pi.inv_apply]
    rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ _, one_smul]
    rwa [← ((meromorphicNF_LaurentPolynomial (divisor f U)) trivial).order_eq_zero_iff,
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
