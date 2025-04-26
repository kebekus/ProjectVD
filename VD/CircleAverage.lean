/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

--import VD.intervalIntegrability

/-!
# Circle Averages

For a function `f` on the complex plane, this file introduces the notation
`circleAverage f c R` as a shorthand for the average of `f` on the circle with
center `c` and radius `R`. Averages of this form are typically used in analysis
of one complex variable. Like `IntervalAverage`, this notion exists as a
convenience, avoiding the hassle to manually elemininate `2 * π` every time an
average is computed.

Note: The relevant integrability property is `CircleIntegrable`, as defined in
`Mathlib.MeasureTheory.Integral.CircleIntegral`.

Implementation Note: Like `circleMap`, `circleAverage`s are defined for negative
radii. The theorem `circleAverage_congr_negRadius` shows that the average is
independent of the radius' sign.
-/

open Filter Metric Real


lemma circleMap_neg {r x : ℝ} {c : ℂ} :
    circleMap c (-r) x = circleMap c r (x + π) := by
  simp [circleMap, add_mul, Complex.exp_add]

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


/-!
# Definition
-/

/--
Define `circleAverage f c R` as the average value of `f` on the circle with
center `c` and radius `R`.
-/
noncomputable def circleAverage (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
  (2 * π)⁻¹ • ∫ θ in (0)..2 * π, f (circleMap c R θ)

/-- Expression in terms of interval averages. -/
lemma circleAverage_eq_intervalAverage {f : ℂ → E} {c : ℂ} {R : ℝ} :
    circleAverage f c R = ⨍ θ in (0)..2 * π, f (circleMap c R θ) := by
  simp_all [circleAverage, interval_average_eq]

/-- Interval averages for zero radii equal values at the center point. -/
@[simp] lemma circleAverage_zeroRadius [CompleteSpace E] {f : ℂ → E} {c : ℂ} :
    circleAverage f c 0 = f c := by
  rw [circleAverage]
  simp only [circleMap_zero_radius, Function.const_apply,
    intervalIntegral.integral_const, sub_zero,
    ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero pi_ne_zero),
    one_smul]

/-!
## Congruence Lemmata
-/

/-- Circle averages do not change when replacing the radius by its negative. -/
theorem circleAverage_congr_negRadius {c : ℂ} {R : ℝ} {f : ℂ → ℝ} :
    circleAverage f c R = circleAverage f c (-R) := by
  unfold circleAverage
  congr 1
  simp_rw [circleMap_neg]
  have t₀ : (fun θ ↦ f (circleMap c R θ)).Periodic (2 * π) :=
    fun x ↦ by simp [periodic_circleMap c R x]
  rw [intervalIntegral.integral_comp_add_right (fun θ ↦ f (circleMap c R θ))]
  have := t₀.intervalIntegral_add_eq 0 π
  rw [zero_add, add_comm] at this
  simp_all

/--
Circle averages do not change when replacing the radius by its absolute value.
-/
theorem circleAverage_congr_absRadius {c : ℂ} {R : ℝ} {f : ℂ → ℝ} :
    circleAverage f c R = circleAverage f c |R| := by
  by_cases hR : 0 ≤ R
  · rw [abs_of_nonneg hR]
  · rw [abs_of_neg (not_le.1 hR), circleAverage_congr_negRadius]

theorem circleAverage_congr_codiscreteWithin {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℝ}
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R ≠ 0) :
    circleAverage f₁ c R = circleAverage f₂ c R := by
  unfold circleAverage
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  apply codiscreteWithin.mono (by tauto) (circleMap_preimage_codiscrete hR hf)

/-!
## Behaviour with Respect to Arithmetic Operations
-/

/-- Circle averages commute with skalar multiplication. -/
theorem circleAverage_smul
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    {a : 𝕜} {c : ℂ} {R : ℝ} {f : ℂ → E} :
    circleAverage (a • f) c R = a • circleAverage f c R := by
  unfold circleAverage
  have := SMulCommClass.symm ℝ 𝕜 E
  rw [smul_comm]
  simp [intervalIntegral.integral_smul]

/-- Circle averages commute with skalar multiplication. -/
theorem circleAverage_smul_fun {c : ℂ} {a R : ℝ} {f : ℂ → E} :
    circleAverage (fun z ↦ a • f z) c R = a • circleAverage f c R := by
  apply circleAverage_smul

/-- Circle averages commute with addition. -/
theorem circleAverage_add {f g : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    circleAverage (f + g) c R = circleAverage f c R + circleAverage g c R := by
  rw [circleAverage, circleAverage, circleAverage, ← smul_add]
  congr
  apply intervalIntegral.integral_add hf hg

/-- Circle averages commute with sums. -/
theorem circleAverage_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ → E}
    {c : ℂ} {R : ℝ} (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    circleAverage (∑ i ∈ s, f i) c R = ∑ i ∈ s, circleAverage (f i) c R := by
  unfold circleAverage
  simp [← Finset.smul_sum, intervalIntegral.integral_finset_sum h]
