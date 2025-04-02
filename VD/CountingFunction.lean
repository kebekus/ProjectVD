/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import VD.ToMathlib.Divisor_add

open MeromorphicOn Metric Real

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]


/-!
# The Counting Function of a Meromorphic Function

For nontrivially normed fields `𝕜`, this file defines the logarithmic counting
function of a meromorphic function defined on `𝕜`, as used in Value
Distribution Theory.
-/

/-!
## Supporting Notation
-/

namespace Function.locallyFinsuppWithin

/--
Shorthand notation for the restriction of a function with locally finite support
within ⊤ to the closed unit ball of radius `r`.
-/
noncomputable def toBall
    (D : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) (r : ℝ) :
    Function.locallyFinsuppWithin (closedBall (0 : 𝕜) |r|) ℤ :=
  D.restrict (by tauto : closedBall (0 : 𝕜) |r| ⊆ ⊤)

/--
Restriction commutes with subtraction.
-/
lemma toBall_sub
    {D₁ D₂ : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ} {r : ℝ} :
    (D₁ - D₂).toBall r = D₁.toBall r - D₂.toBall r := by
  ext x
  by_cases h₁ : ‖x‖ ≤ |r| <;> simp [toBall, restrict_apply, h₁]

end Function.locallyFinsuppWithin

/-!
## The Logarithmic Counting Function of a Function with Locally Finite Support
-/

/--
Definition of the logarithmic counting function for a function with locally
finite support within `⊤`.
-/
noncomputable def Function.locallyFinsuppWithin.logCounting
    (D : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) :
    ℝ → ℝ :=
  fun r ↦ ∑ᶠ z, D.toBall r z * log (r * ‖z‖⁻¹) + (D 0) * log r

/-- The value of the counting function at zero is zero. -/
@[simp] lemma Function.locallyFinsuppWithin.logCounting_eval_zero
    (D : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) :
    logCounting D 0 = 0 := by
  rw [logCounting]
  simp

/--
The logarithmic counting function commutes with subtraction.
-/
@[simp] lemma Function.locallyFinsuppWithin.logCounting_sub [ProperSpace 𝕜]
    (D₁ D₂ : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) :
    logCounting (D₁ - D₂) = logCounting D₁ - logCounting D₂ := by
  ext r
  simp [logCounting]
  have h₁s : ((D₁.toBall r).support ∪ (D₂.toBall r).support).Finite := by
    apply Set.finite_union.2
    constructor
    <;> apply Function.locallyFinsuppWithin.finiteSupport _ (isCompact_closedBall 0 |r|)
  have t₁ : (fun z ↦ D₁.toBall r z * log (r * ‖z‖⁻¹)).support ⊆ h₁s.toFinset := by
    intro x hx
    simp_all
  rw [finsum_eq_sum_of_support_subset _ t₁]
  have t₂ : (fun z ↦ D₂.toBall r z * log (r * ‖z‖⁻¹)).support ⊆ h₁s.toFinset := by
    intro x hx
    simp_all
  rw [finsum_eq_sum_of_support_subset _ t₂]
  have t₁₂ : (fun z ↦ (D₁ - D₂).toBall r z * log (r * ‖z‖⁻¹)).support ⊆ h₁s.toFinset := by
    intro x hx
    by_contra hCon
    rw [Function.locallyFinsuppWithin.toBall_sub] at hx
    simp_all
  simp_rw [finsum_eq_sum_of_support_subset _ t₁₂]
  have {A B C D : ℝ} : A + B - (C + D) = A - C + (B - D) := by
    ring
  simp_rw [this, ← Finset.sum_sub_distrib, ← sub_mul, Function.locallyFinsuppWithin.toBall_sub]
  simp

/-!
## The Logarithmic Counting Function of a Meromorphic Function
-/

namespace VD

/-- The logarithmic counting function of a meromorphic function. -/
noncomputable def logCounting (f : 𝕜 → E) (a : WithTop E) :
    ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact (divisor f ⊤)⁻.logCounting
  · exact (divisor (fun z ↦ f z - a.untop₀) ⊤)⁺.logCounting

lemma logCounting_finite {f : 𝕜 → E} {a : E} :
    logCounting f a = (divisor (fun z ↦ f z - a) ⊤)⁺.logCounting := by
  simp [logCounting]

lemma logCounting_finite_eq_logCounting_zero_of_shifted {f : 𝕜 → E} {a : E} :
    logCounting f a = logCounting (f - fun _ ↦ a) 0 := by
  simp [logCounting]

lemma logCounting_zero {f : 𝕜 → E} :
    logCounting f 0 = (divisor f ⊤)⁺.logCounting := by
  simp [logCounting]

lemma logCounting_top {f : 𝕜 → E} :
    logCounting f ⊤ = (divisor f ⊤)⁻.logCounting := by
  simp [logCounting]

lemma logCounting_eval_zero {f : 𝕜 → E} {a : WithTop E}:
    logCounting f a 0 = 0 := by
  by_cases h : a = ⊤ <;> simp [h, logCounting]

theorem log_counting_zero_sub_logCounting_top [ProperSpace 𝕜] {f : 𝕜 → E} :
    (divisor f ⊤).logCounting = logCounting f 0 - logCounting f ⊤ := by
  simp [logCounting_zero, logCounting_top, ← Function.locallyFinsuppWithin.logCounting_sub]

/-!
## Elementary Properties of the Counting Function
-/

theorem logCounting_inv [CompleteSpace 𝕜] {f : 𝕜 → 𝕜} :
    logCounting f 0 = logCounting f⁻¹ ⊤ := by
  simp [logCounting_zero, logCounting_top]

theorem logCounting_add_analytic {f g : 𝕜 → E} (hf : MeromorphicOn f ⊤)
    (hg : AnalyticOn 𝕜 g ⊤) :
    logCounting (f + g) ⊤ = logCounting f ⊤ := by
  simp only [logCounting, ↓reduceDIte,
    hf.divisor_add_analytic (isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg)]

theorem logCounting_add_const {f : 𝕜 → E} {a : E} (hf : MeromorphicOn f ⊤) :
    logCounting (f + fun _ ↦ a) ⊤ = logCounting f ⊤ := by
  apply logCounting_add_analytic hf analyticOn_const

theorem logCounting_sub_const {f : 𝕜 → E} {a : E} (hf : MeromorphicOn f ⊤) :
    logCounting (f - fun _ ↦ a) ⊤ = logCounting f ⊤ := by
  have : f - (fun x ↦ a) = f + fun x ↦ -a := by
    funext x
    simp [sub_eq_add_neg]
  rw [this]
  apply logCounting_add_analytic hf analyticOn_const

end VD
