/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import VD.ToMathlib.Divisor_add

open Metric Real

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
## Definition of the Counting Function
-/

noncomputable def Function.locallyFinsuppWithin.restr_to_ball
    (D : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) (r : ℝ) :
    Function.locallyFinsuppWithin (closedBall (0 : 𝕜) |r|) ℤ :=
  D.restrict (by tauto : closedBall (0 : 𝕜) |r| ⊆ ⊤)

/--
The logarithmic counting function of a function with locally finite support
within `⊤`.
-/
noncomputable def Function.locallyFinsuppWithin.logCounting
    (D : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) :
    ℝ → ℝ :=
  fun r ↦ ∑ᶠ z, D.restr_to_ball r z * (log r - log ‖z‖)

/-- The value of the counting function at zero is zero. -/
@[simp] lemma Function.locallyFinsuppWithin.logCounting_eval_zero
    (D : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) :
    logCounting D 0 = 0 := by
  rw [logCounting, finsum_eq_zero_of_forall_eq_zero]
  intro x
  by_cases hx : x = 0
  <;> simp [hx]

lemma Function.locallyFinsuppWithin.logCounting_support {r : ℝ}
    (D : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) :
    Function.support (fun z ↦ D.restr_to_ball r z * (log r - log ‖z‖))
      ⊆ Function.support (D.restr_to_ball r) := by
  intro x hx
  simp_all

@[simp] lemma Function.locallyFinsuppWithin.logCounting_sub
    (D₁ D₂ : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) :
    logCounting D₁ - logCounting D₂ = logCounting (D₁ - D₂) := by
  ext r
  simp [logCounting]
  let s := (D₁.restr_to_ball r).support ∪ (D₂.restr_to_ball r).support
  have t₁ : (fun z ↦ D₁.restr_to_ball r z * (log r - log ‖z‖)).support ⊆ s := by
    intro x hx
    simp_all [s]
  have t₂ : (fun z ↦ D₂.restr_to_ball r z * (log r - log ‖z‖)).support ⊆ s := by
    intro x hx
    simp_all [s]
  have t₁₂ : (fun z ↦ (D₁ - D₂).restr_to_ball r z * (log r - log ‖z‖)).support ⊆ s := by
    intro x hx
    simp_all [s]

    sorry
  rw [finsum_eq_sum]
  sorry
  sorry

-- TODO: Integral representation

namespace MeromorphicOn

/-- The logarithmic counting function of a meromorphic function. -/
noncomputable def logCounting (f : 𝕜 → E) (a : WithTop E) :
    ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact (divisor f ⊤)⁻.logCounting
  · exact (divisor (fun z ↦ f z - a.untop₀) ⊤)⁺.logCounting

lemma logCounting_def {f : 𝕜 → E} {a : E} :
    logCounting f a = (divisor (fun z ↦ f z - a) ⊤)⁺.logCounting := by
  simp [logCounting]

lemma logCounting_def_zero {f : 𝕜 → E} :
    logCounting f 0 = (divisor f ⊤)⁺.logCounting := by
  simp [logCounting]

lemma logCounting_def_top {f : 𝕜 → E} :
    logCounting f ⊤ = (divisor f ⊤)⁻.logCounting := by
  simp [logCounting]

lemma logCounting_eval_zero {f : 𝕜 → E} {a : WithTop E}:
    logCounting f a 0 = 0 := by
  by_cases h : a = ⊤ <;> simp [h, logCounting]

theorem log_counting_zero_sub_logCounting_top {f : 𝕜 → E} :
    logCounting f 0 - logCounting f ⊤ = (divisor f ⊤).logCounting := by
  simp [logCounting_def_zero, logCounting_def_top]

/-!
## Elementary Properties of the Counting Function
-/

theorem logCounting_inv [CompleteSpace 𝕜] {f : 𝕜 → 𝕜} :
    logCounting f 0 = logCounting f⁻¹ ⊤ := by
  simp [logCounting_def_zero, logCounting_def_top]

theorem logCounting_add_analytic {f g : 𝕜 → E} (hf : MeromorphicOn f ⊤)
    (hg : AnalyticOn 𝕜 g ⊤) :
    logCounting (f + g) ⊤ = logCounting f ⊤ := by
  simp only [logCounting, ↓reduceDIte,
    hf.divisor_add_analytic ((IsOpen.analyticOn_iff_analyticOnNhd TopologicalSpace.isOpen_univ).1 hg)]

theorem logCounting_add_const {f : 𝕜 → E} {a : E} (hf : MeromorphicOn f ⊤) :
    logCounting (f + fun _ ↦ a) ⊤ = logCounting f ⊤ := by
  apply hf.logCounting_add_analytic analyticOn_const

end MeromorphicOn
