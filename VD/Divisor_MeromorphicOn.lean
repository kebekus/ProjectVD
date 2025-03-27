import Mathlib.Analysis.Meromorphic.Divisor
import VD.ToMathlib.NormalForm

open Classical Filter Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {U : Set 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace MeromorphicOn

/-- If `f₁` is meromorphic on `U`, if `f₂` agrees with `f₁` on a codiscrete
  subset of `U` and outside of `U`, then `f₂` is also meromorphic on `U`. -/
theorem congr_codiscreteWithin {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂) (h₂ : Set.EqOn f₁ f₂ Uᶜ) :
    MeromorphicOn f₂ U := by
  intro x hx
  apply (hf₁ x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  filter_upwards [h₁ x hx] with a ha
  simp at ha
  tauto

/-- If `f₁` is meromorphic on an open set `U`, if `f₂` agrees with `f₁` on a
  codiscrete subset of `U`, then `f₂` is also meromorphic on `U`. -/
theorem congr_codiscreteWithin_open {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂) (h₂ : IsOpen U) :
    MeromorphicOn f₂ U := by
  intro x hx
  apply (hf₁ x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  have : U ∈ 𝓝[≠] x := by
    apply mem_nhdsWithin.mpr
    use U, h₂, hx, Set.inter_subset_left
  filter_upwards [this, h₁ x hx] with a h₁a h₂a
  simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_setOf_eq, not_and, Decidable.not_not] at h₂a
  tauto

/-- If `f₁` is meromorphic on `U`, if `f₂` agrees with `f₁` on a codiscrete
  subset of `U` and outside of `U`, then `f₁` and `f₂` induce the same
  divisors on `U`. -/
theorem divisor_congr_codiscreteWithin [CompleteSpace E] {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (h₁ : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) (h₂ : Set.EqOn f₁ f₂ Uᶜ) :
    divisor f₁ U = divisor f₂ U := by
  ext x
  by_cases hx : x ∈ U <;> simp [hf₁, hf₁.congr_codiscreteWithin h₁ h₂, hx]
  · congr 1
    apply (hf₁ x hx).order_congr
    simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
      disjoint_principal_right] at h₁
    filter_upwards [h₁ x hx] with a ha
    simp at ha
    tauto

/--
If `f₁` is meromorphic on an open set `U`, if `f₂` agrees with `f₁` on a
codiscrete subset of `U`, then `f₁` and `f₂` induce the same divisors on`U`.
-/
theorem divisor_congr_codiscreteWithin_open [CompleteSpace E] {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicOn f₁ U) (h₁ : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) (h₂ : IsOpen U) :
    divisor f₁ U = divisor f₂ U := by
  ext x
  by_cases hx : x ∈ U <;> simp [hf₁, hf₁.congr_codiscreteWithin_open h₁ h₂, hx]
  · congr 1
    apply (hf₁ x hx).order_congr
    simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
      disjoint_principal_right] at h₁
    have : U ∈ 𝓝[≠] x := by
      apply mem_nhdsWithin.mpr
      use U, h₂, hx, Set.inter_subset_left
    filter_upwards [this, h₁ x hx] with a h₁a h₂a
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_setOf_eq, not_and, Decidable.not_not] at h₂a
    tauto

/-- Taking the divisor of a meromorphic function commutes with restriction. -/
theorem divisor_restrict [CompleteSpace E] {f : 𝕜 → E} {V : Set 𝕜} (hf : MeromorphicOn f U) (hV : V ⊆ U) :
    (divisor f U).restrict hV = divisor f V := by
  ext x
  by_cases hx : x ∈ V
  · rw [Function.locallyFinsuppWithin.restrict_apply]
    simp [hf, hx, hf.mono_set hV, hV hx]
  · simp [hx]

-- ----------------

/--
Conversion to normal form on `U` does not affect the divisor.
-/
theorem divisor_toMeromorphicNFOn [CompleteSpace E] {f : 𝕜 → E} (hf : MeromorphicOn f U) :
    MeromorphicOn.divisor f U = MeromorphicOn.divisor (toMeromorphicNFOn f U) U := by
  rw [← hf.divisor_congr_codiscreteWithin (toMeromorphicNFOn_eqOn_codiscrete hf)]
  exact toMeromorphicNFOn_eq_self_on_compl hf
