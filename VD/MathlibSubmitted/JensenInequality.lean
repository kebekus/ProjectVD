/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Circle-Average Estimates — LLD work packages C1–C2

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §5.

Mathlib target: extend `Mathlib/MeasureTheory/Integral/CircleAverage.lean` and/or the `PosLog`
integrals files. Dependencies: none (independently PR-able).

This file provides the two circle-average estimates used in the proof of the two-radius bound for
the Lemma on the Logarithmic Derivative.

- `Real.circleAverage_posLog_le_posLog_circleAverage` (C1): Jensen's inequality specialised to
  circle averages. For nonnegative circle-integrable `u`, the average of `log⁺ u` is at most
  `log⁺` of the average, up to an additive constant `log 2`. The proof squeezes `log⁺` between
  `log (1 + ·)` and `log (1 + ·) - log 2` and applies `ConcaveOn.le_map_average` to the concave
  function `log (1 + ·)` on `Set.Ici 0`.

- `Real.circleIntegrable_norm_sub_rpow`, `Real.circleAverage_norm_sub_rpow_le` (C2): **uniformly
  in `a : ℂ`**, the circle average of `‖· - a‖ ^ (-2⁻¹)` over the circle of radius `r > 0` is
  bounded by `4 * r ^ (-2⁻¹)`. This uniformity is why the exponent-1/2 trick is used for the
  divisor sums in the two-radius estimate: the average of `‖· - a‖⁻¹` is *not* uniformly bounded.
  The proof combines the elementary estimate `‖circleMap 0 r (θ + arg a) - a‖ ≥ (r/2) * |sin (θ/2)|`
  (valid for **all** `a`) with the Jordan inequality `Real.mul_le_sin`, majorizing the integrand
  by `(r/(2π) * θ) ^ (-2⁻¹) + (r/(2π) * (2π - θ)) ^ (-2⁻¹)`, whose integral is computed exactly.
-/

open Complex Filter MeasureTheory Metric Real Set

/-!(
## C1: Jensen's Inequality for Circle Averages of `log⁺`
-/

private lemma circleIntegrable_posLog_comp {u : ℂ → ℝ} {r : ℝ} (hu : CircleIntegrable u 0 r) :
    CircleIntegrable (log⁺ ∘ u) 0 r := by
  apply IntervalIntegrable.mono_fun (IntervalIntegrable.abs hu)
  · exact continuous_posLog.comp_aestronglyMeasurable
      (intervalIntegrable_iff.1 hu).aestronglyMeasurable
  · filter_upwards with θ
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg posLog_nonneg]
    exact posLog_le_abs _

private lemma circleIntegrable_log_one_add {u : ℂ → ℝ} {r : ℝ}
    (h₀ : ∀ z ∈ sphere (0 : ℂ) |r|, 0 ≤ u z) (hu : CircleIntegrable u 0 r) :
    CircleIntegrable (fun z ↦ Real.log (1 + u z)) 0 r := by
  apply IntervalIntegrable.mono_fun (IntervalIntegrable.abs hu)
  · apply AEMeasurable.aestronglyMeasurable
    exact Real.measurable_log.comp_aemeasurable
      (aemeasurable_const.add (intervalIntegrable_iff.1 hu).aestronglyMeasurable.aemeasurable)
  · filter_upwards with θ
    have h₁ : 0 ≤ u (circleMap 0 r θ) := h₀ _ (circleMap_mem_sphere' 0 r θ)
    have h₂ := log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + u (circleMap 0 r θ))
    simp only [Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg (log_nonneg (by linarith))]
    calc Real.log (1 + u (circleMap 0 r θ))
        ≤ u (circleMap 0 r θ) := by linarith
      _ ≤ |u (circleMap 0 r θ)| := le_abs_self _

private lemma concaveOn_log_one_add : ConcaveOn ℝ (Ici 0) (fun x ↦ Real.log (1 + x)) :=
  (strictConcaveOn_log_Ioi.concaveOn.translate_right 1).subset
    (fun x hx ↦ by simpa using by linarith [mem_Ici.1 hx]) (convex_Ici 0)

/--
**Jensen's inequality for circle averages**: for a nonnegative circle-integrable function `u`, the
circle average of `log⁺ u` is at most `log⁺` of the circle average, up to an additive constant `log
2`.
-/
theorem Real.circleAverage_posLog_le_posLog_circleAverage {u : ℂ → ℝ} {r : ℝ}
    (h₀ : ∀ z ∈ sphere (0 : ℂ) |r|, 0 ≤ u z) (hu : CircleIntegrable u 0 r) :
    circleAverage (log⁺ ∘ u) 0 r ≤ log⁺ (circleAverage u 0 r) + Real.log 2 := by
  have hInt : CircleIntegrable (fun z ↦ log (1 + u z)) 0 r :=
    circleIntegrable_log_one_add h₀ hu
  have hIntP : CircleIntegrable (log⁺ ∘ u) 0 r := circleIntegrable_posLog_comp hu
  have step₁ : circleAverage (log⁺ ∘ u) 0 r ≤ circleAverage (fun z ↦ log (1 + u z)) 0 r :=
    circleAverage_mono hIntP hInt (fun z hz ↦ posLog_le_log_one_add (h₀ z hz))
  -- Jensen's inequality, applied to the interval average over `Ι 0 (2 * π)`
  have step₂ : circleAverage (fun z ↦ log (1 + u z)) 0 r
      ≤ log (1 + circleAverage u 0 r) := by
    rw [circleAverage_eq_intervalAverage, circleAverage_eq_intervalAverage]
    exact concaveOn_log_one_add.le_map_set_average
      (ContinuousOn.log (by fun_prop)
        (fun x hx ↦ by simp only [mem_Ici] at hx; exact (by linarith : (0:ℝ) < 1 + x).ne'))
      isClosed_Ici (by simp [uIoc_of_le Real.two_pi_pos.le, Real.pi_pos])
      (by rw [uIoc_of_le Real.two_pi_pos.le]; exact measure_Ioc_lt_top.ne)
      (ae_restrict_of_forall_mem measurableSet_uIoc
        fun θ _ ↦ h₀ _ (circleMap_mem_sphere' 0 r θ))
      (intervalIntegrable_iff.1 hu) (intervalIntegrable_iff.1 hInt)
  have step₃ := log_one_add_le_posLog (x := circleAverage u 0 r)
  linarith
