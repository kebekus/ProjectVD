/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Jensen's Inequality for Circle Averages of `log⁺` — LLD work package C1

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §5. The companion work package C2 (uniform bounds for
circle averages of `‖· - a‖ ^ p`) lives in `VD/LLD/CircleAverageEstimates.lean`.

Mathlib target: extend `Mathlib/MeasureTheory/Integral/CircleAverage.lean`. Dependencies: none
(independently PR-able).

## Main result

- `Real.circleAverage_posLog_le_posLog_circleAverage`: Jensen's inequality specialised to circle
  averages. For nonnegative circle-integrable `u`, the average of `log⁺ u` is at most `log⁺` of the
  average, up to an additive constant `log 2`. The proof squeezes `log⁺` between `log (1 + ·)` and
  `log (1 + ·) - log 2` and applies `ConcaveOn.le_map_set_average` to the concave function
  `log (1 + ·)` on `Set.Ici 0`.
-/

open Complex Filter MeasureTheory Metric Real Set

/-!
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
