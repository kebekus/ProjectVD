/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

/-- The logarithmic counting function of a function with locally finite support `⊤`. -/
noncomputable def Function.locallyFinsuppWithin.logCounting
    (D : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) :
    ℝ → ℝ :=
  fun r ↦ ∑ᶠ z, D.restrict (by tauto : closedBall (0 : 𝕜) |r| ⊆ ⊤) z * (log r - log ‖z‖)

/-- The value of the counting function at zero is zero. -/
@[simp] lemma Function.locallyFinsuppWithin.logCounting_eval_zero
    (D : Function.locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) :
    logCounting D 0 = 0 := by
  rw [logCounting, finsum_eq_zero_of_forall_eq_zero]
  intro x
  by_cases hx : x = 0
  <;> simp [hx]


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

/-!
## Elementary Properties of the Counting Function
-/

theorem logCounting_inv [CompleteSpace 𝕜] {f : 𝕜 → 𝕜} :
    logCounting f 0 = logCounting f⁻¹ ⊤ := by
  rw [logCounting_def_zero, logCounting_def_top]
  have : (divisor f ⊤)⁺ = (divisor f⁻¹ ⊤)⁻ := by
    ext x
    simp
  rw [this]

theorem logCounting_add_analytic {f g : 𝕜 → E} (hf : MeromorphicOn f ⊤)
    (hg : AnalyticOn 𝕜 g ⊤) :
    logCounting (f + g) ⊤ = logCounting f ⊤ := by
  sorry

end MeromorphicOn
