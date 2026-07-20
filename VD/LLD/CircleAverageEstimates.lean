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

private lemma posLog_le_log_one_add {x : ℝ} (hx : 0 ≤ x) : log⁺ x ≤ Real.log (1 + x) := by
  rw [posLog_apply]
  apply max_le (Real.log_nonneg (by linarith))
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  · exact Real.log_le_log hx' (by linarith)

private lemma log_one_add_le_posLog {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ log⁺ x + Real.log 2 := by
  rw [posLog_eq_log_max_one hx]
  have h₁ : (1 : ℝ) + x ≤ max 1 x * 2 := by
    rcases le_total x 1 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith
  calc Real.log (1 + x)
      ≤ Real.log (max 1 x * 2) := Real.log_le_log (by linarith) h₁
    _ = Real.log (max 1 x) + Real.log 2 :=
        Real.log_mul (by positivity) two_ne_zero

private lemma posLog_le_abs (x : ℝ) : log⁺ x ≤ |x| := by
  rcases le_or_gt |x| 1 with h | h
  · rw [(posLog_eq_zero_iff x).2 h]
    exact abs_nonneg x
  · rw [← posLog_abs, posLog_eq_log (by rw [abs_abs]; exact h.le)]
    linarith [Real.log_le_sub_one_of_pos (lt_trans one_pos h : (0:ℝ) < |x|)]

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
    have h₂ := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + u (circleMap 0 r θ))
    simp only [Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
    calc Real.log (1 + u (circleMap 0 r θ))
        ≤ u (circleMap 0 r θ) := by linarith
      _ ≤ |u (circleMap 0 r θ)| := le_abs_self _

private lemma concaveOn_log_one_add : ConcaveOn ℝ (Ici 0) (fun x ↦ Real.log (1 + x)) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simp only [mem_Ici] at hx hy
  simp only [smul_eq_mul]
  have h₃ := strictConcaveOn_log_Ioi.concaveOn.2 (mem_Ioi.2 (by linarith : (0:ℝ) < 1 + x))
    (mem_Ioi.2 (by linarith : (0:ℝ) < 1 + y)) ha hb hab
  simp only [smul_eq_mul] at h₃
  have h₄ : a * (1 + x) + b * (1 + y) = 1 + (a * x + b * y) := by linear_combination hab
  rwa [h₄] at h₃

/-- **Jensen's inequality for circle averages**: for a nonnegative circle-integrable function
`u`, the circle average of `log⁺ u` is at most `log⁺` of the circle average, up to an additive
constant `log 2`. -/
theorem Real.circleAverage_posLog_le_posLog_circleAverage {u : ℂ → ℝ} {r : ℝ}
    (h₀ : ∀ z ∈ sphere (0 : ℂ) |r|, 0 ≤ u z) (hu : CircleIntegrable u 0 r) :
    circleAverage (log⁺ ∘ u) 0 r ≤ log⁺ (circleAverage u 0 r) + Real.log 2 := by
  have hInt : CircleIntegrable (fun z ↦ Real.log (1 + u z)) 0 r :=
    circleIntegrable_log_one_add h₀ hu
  have hIntP : CircleIntegrable (log⁺ ∘ u) 0 r := circleIntegrable_posLog_comp hu
  have step₁ : circleAverage (log⁺ ∘ u) 0 r ≤ circleAverage (fun z ↦ Real.log (1 + u z)) 0 r :=
    circleAverage_mono hIntP hInt (fun z hz ↦ posLog_le_log_one_add (h₀ z hz))
  -- Jensen's inequality for the average with respect to `volume.restrict (Ioc 0 (2 * π))`
  set μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hμ_def
  have hμ_univ : μ univ = ENNReal.ofReal (2 * π) := by
    rw [hμ_def, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  have hμ_ne : NeZero μ := by
    constructor
    rw [← Measure.measure_univ_ne_zero, hμ_univ]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hμ_real : μ.real univ = 2 * π := by
    rw [measureReal_def, hμ_univ, ENNReal.toReal_ofReal (by positivity)]
  have bridge : ∀ v : ℂ → ℝ, circleAverage v 0 r = ⨍ θ, v (circleMap 0 r θ) ∂μ := by
    intro v
    rw [circleAverage_def, average_eq, hμ_real, intervalIntegral.integral_of_le (by positivity)]
  have hfi : Integrable (fun θ ↦ u (circleMap 0 r θ)) μ := by
    have h₁ := intervalIntegrable_iff.1 hu
    rwa [uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * π)] at h₁
  have hgi : Integrable (fun θ ↦ Real.log (1 + u (circleMap 0 r θ))) μ := by
    have h₁ := intervalIntegrable_iff.1 hInt
    rwa [uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * π)] at h₁
  have step₂ : circleAverage (fun z ↦ Real.log (1 + u z)) 0 r
      ≤ Real.log (1 + circleAverage u 0 r) := by
    rw [bridge (fun z ↦ Real.log (1 + u z)), bridge u]
    exact concaveOn_log_one_add.le_map_average
      (ContinuousOn.log (by fun_prop)
        (fun x hx ↦ by simp only [mem_Ici] at hx; exact (by linarith : (0:ℝ) < 1 + x).ne'))
      isClosed_Ici
      (Eventually.of_forall fun θ ↦ h₀ _ (circleMap_mem_sphere' 0 r θ))
      hfi hgi
  have step₃ := log_one_add_le_posLog (circleAverage_nonneg_of_nonneg h₀)
  linarith

/-!
## C2: The Uniform Bound for the Singular Integrand
-/

/-- Rotating the circle moves the base point of the distance function to the positive real
axis. -/
private lemma norm_circleMap_add_arg_sub {a : ℂ} {r : ℝ} (θ : ℝ) :
    ‖circleMap 0 r (θ + Complex.arg a) - a‖ = ‖circleMap 0 r θ - (‖a‖ : ℂ)‖ := by
  have ha : (‖a‖ : ℂ) * Complex.exp (Complex.arg a * Complex.I) = a :=
    Complex.norm_mul_exp_arg_mul_I a
  have hc : circleMap 0 r (θ + Complex.arg a)
      = circleMap 0 r θ * Complex.exp (Complex.arg a * Complex.I) := by
    simp only [circleMap, zero_add]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  rw [hc]
  calc ‖circleMap 0 r θ * Complex.exp (Complex.arg a * Complex.I) - a‖
      = ‖(circleMap 0 r θ - (‖a‖ : ℂ)) * Complex.exp (Complex.arg a * Complex.I)‖ := by
        rw [sub_mul, ha]
    _ = ‖circleMap 0 r θ - (‖a‖ : ℂ)‖ := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Elementary estimate: on the circle of radius `r` around `0`, the distance to any point on the
nonnegative real axis is at least `(r/2) * |sin (θ/2)|`. -/
private lemma le_norm_circleMap_sub_ofReal {r : ℝ} (hr : 0 < r) (θ s : ℝ) (hs : 0 ≤ s) :
    r / 2 * |Real.sin (θ / 2)| ≤ ‖circleMap 0 r θ - (s : ℂ)‖ := by
  have hre : (circleMap 0 r θ - (s : ℂ)).re = r * Real.cos θ - s := by
    simp [circleMap, Complex.exp_ofReal_mul_I_re]
  have him : (circleMap 0 r θ - (s : ℂ)).im = r * Real.sin θ := by
    simp [circleMap, Complex.exp_ofReal_mul_I_im]
  have hsq : ‖circleMap 0 r θ - (s : ℂ)‖ ^ 2
      = (r - s) ^ 2 + 4 * r * s * Real.sin (θ / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have h₁ := Real.sin_sq_add_cos_sq θ
    have h₂ := Real.sin_sq_eq_half_sub (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h₂
    linear_combination r ^ 2 * h₁ - 4 * r * s * h₂
  have hle : (r / 2 * |Real.sin (θ / 2)|) ^ 2 ≤ ‖circleMap 0 r θ - (s : ℂ)‖ ^ 2 := by
    rw [hsq, mul_pow, sq_abs]
    nlinarith [mul_nonneg (sub_nonneg.2 (Real.sin_sq_le_one (θ / 2))) (sq_nonneg (r - s)),
      mul_nonneg (mul_nonneg (mul_nonneg hr.le hs) (sq_nonneg (Real.sin (θ / 2))))
        (by norm_num : (0:ℝ) ≤ 4),
      mul_nonneg (sq_nonneg (Real.sin (θ / 2))) (sq_nonneg r),
      mul_nonneg (sq_nonneg (Real.sin (θ / 2))) (sq_nonneg s),
      mul_nonneg (mul_nonneg hr.le hs) (sq_nonneg (Real.sin (θ / 2)))]
  calc r / 2 * |Real.sin (θ / 2)|
      = √((r / 2 * |Real.sin (θ / 2)|) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ √(‖circleMap 0 r θ - (s : ℂ)‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = ‖circleMap 0 r θ - (s : ℂ)‖ := Real.sqrt_sq (norm_nonneg _)

/-- The **universal** lower bound: for every `a : ℂ`, points on the circle of radius `r` keep
distance at least `(r/2) * |sin (θ/2)|` from `a`, where `θ` is measured from `arg a`. -/
private lemma le_norm_circleMap_add_arg_sub {a : ℂ} {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    r / 2 * |Real.sin (θ / 2)| ≤ ‖circleMap 0 r (θ + Complex.arg a) - a‖ := by
  rw [norm_circleMap_add_arg_sub θ]
  exact le_norm_circleMap_sub_ofReal hr θ ‖a‖ (norm_nonneg a)

/-- Pointwise majorization of the singular integrand by an explicitly integrable function. -/
private lemma rpow_norm_circleMap_le {a : ℂ} {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (2 * π)) :
    ‖circleMap 0 r (θ + Complex.arg a) - a‖ ^ (-(2:ℝ)⁻¹)
      ≤ (r / (2 * π) * θ) ^ (-(2:ℝ)⁻¹) + (r / (2 * π) * (2 * π - θ)) ^ (-(2:ℝ)⁻¹) := by
  obtain ⟨h₁, h₂⟩ := hθ
  rcases le_total θ π with h | h
  · have h₃ : r / (2 * π) * θ ≤ r / 2 * |Real.sin (θ / 2)| := by
      have h₄ := Real.mul_le_sin (x := θ / 2) (by linarith) (by linarith)
      have h₅ : 0 ≤ Real.sin (θ / 2) :=
        le_trans (mul_nonneg (by positivity) (by linarith)) h₄
      rw [abs_of_nonneg h₅]
      calc r / (2 * π) * θ = r / 2 * (2 / π * (θ / 2)) := by field_simp
        _ ≤ r / 2 * Real.sin (θ / 2) := by gcongr
    have h₆ : (0:ℝ) < r / (2 * π) * θ := mul_pos (by positivity) h₁
    have h₇ := Real.rpow_le_rpow_of_nonpos h₆
      (le_trans h₃ (le_norm_circleMap_add_arg_sub (a := a) hr θ)) (by norm_num : -(2:ℝ)⁻¹ ≤ 0)
    refine h₇.trans (le_add_of_nonneg_right (Real.rpow_nonneg ?_ _))
    exact mul_nonneg (by positivity) (by linarith)
  · have hsin : Real.sin (θ / 2) = Real.sin ((2 * π - θ) / 2) := by
      rw [show (2 * π - θ) / 2 = π - θ / 2 by ring, Real.sin_pi_sub]
    have h₃ : r / (2 * π) * (2 * π - θ) ≤ r / 2 * |Real.sin (θ / 2)| := by
      have h₄ := Real.mul_le_sin (x := (2 * π - θ) / 2) (by linarith) (by linarith)
      have h₅ : 0 ≤ Real.sin ((2 * π - θ) / 2) :=
        le_trans (mul_nonneg (by positivity) (by linarith)) h₄
      rw [hsin, abs_of_nonneg h₅]
      calc r / (2 * π) * (2 * π - θ)
          = r / 2 * (2 / π * ((2 * π - θ) / 2)) := by field_simp
        _ ≤ r / 2 * Real.sin ((2 * π - θ) / 2) := by gcongr
    have h₆ : (0:ℝ) < r / (2 * π) * (2 * π - θ) := mul_pos (by positivity) (by linarith)
    have h₇ := Real.rpow_le_rpow_of_nonpos h₆
      (le_trans h₃ (le_norm_circleMap_add_arg_sub (a := a) hr θ)) (by norm_num : -(2:ℝ)⁻¹ ≤ 0)
    refine h₇.trans (le_add_of_nonneg_left (Real.rpow_nonneg ?_ _))
    exact mul_nonneg (by positivity) (by linarith)

/-- The first piece of the majorant is interval integrable. -/
private lemma intervalIntegrable_majorant_left {r : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun θ : ℝ ↦ (r / (2 * π) * θ) ^ (-(2:ℝ)⁻¹)) volume 0 (2 * π) := by
  have h₁ : IntervalIntegrable (fun x : ℝ ↦ x ^ (-(2:ℝ)⁻¹)) volume 0 r :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h₂ := h₁.comp_mul_left (c := r / (2 * π))
  have h₃ : r / (r / (2 * π)) = 2 * π := by
    rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hr.ne', mul_one]
  simpa [h₃] using h₂

/-- The majorant is interval integrable. -/
private lemma intervalIntegrable_majorant {r : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun θ ↦ (r / (2 * π) * θ) ^ (-(2:ℝ)⁻¹)
      + (r / (2 * π) * (2 * π - θ)) ^ (-(2:ℝ)⁻¹)) volume 0 (2 * π) := by
  apply IntervalIntegrable.add (intervalIntegrable_majorant_left hr)
  have h₁ := (intervalIntegrable_majorant_left hr).comp_sub_left (2 * π)
  simpa using h₁.symm

/-- The exact value of the majorant's integral. -/
private lemma integral_majorant {r : ℝ} (hr : 0 < r) :
    (∫ θ in (0:ℝ)..2 * π, ((r / (2 * π) * θ) ^ (-(2:ℝ)⁻¹)
      + (r / (2 * π) * (2 * π - θ)) ^ (-(2:ℝ)⁻¹))) = 8 * π * r ^ (-(2:ℝ)⁻¹) := by
  have hπ : (0:ℝ) < 2 * π := by positivity
  rw [intervalIntegral.integral_add (intervalIntegrable_majorant_left hr)
    (by simpa using ((intervalIntegrable_majorant_left hr).comp_sub_left (2 * π)).symm)]
  have e₂ : (∫ θ in (0:ℝ)..2 * π, (r / (2 * π) * (2 * π - θ)) ^ (-(2:ℝ)⁻¹))
      = ∫ θ in (0:ℝ)..2 * π, (r / (2 * π) * θ) ^ (-(2:ℝ)⁻¹) := by
    have h₁ := intervalIntegral.integral_comp_sub_left (a := 0) (b := 2 * π)
      (fun θ ↦ (r / (2 * π) * θ) ^ (-(2:ℝ)⁻¹)) (2 * π)
    simpa using h₁
  have e₁ : (∫ θ in (0:ℝ)..2 * π, (r / (2 * π) * θ) ^ (-(2:ℝ)⁻¹)) = 4 * π * r ^ (-(2:ℝ)⁻¹) := by
    have h₀ : r / (2 * π) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun x ↦ x ^ (-(2:ℝ)⁻¹)) h₀]
    have h₁ : r / (2 * π) * (2 * π) = r := by field_simp
    rw [mul_zero, h₁, integral_rpow (Or.inl (by norm_num)),
      show -(2:ℝ)⁻¹ + 1 = 2⁻¹ by norm_num, Real.zero_rpow (by norm_num), sub_zero, smul_eq_mul,
      inv_div]
    have h₂ : r ^ ((2:ℝ)⁻¹) / r = r ^ (-(2:ℝ)⁻¹) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one r, ← Real.rpow_add hr]
      norm_num
    calc 2 * π / r * (r ^ ((2:ℝ)⁻¹) / 2⁻¹)
        = 4 * π * (r ^ ((2:ℝ)⁻¹) / r) := by ring
      _ = 4 * π * r ^ (-(2:ℝ)⁻¹) := by rw [h₂]
  rw [e₂, e₁]
  ring

/-- Almost every point of the interval of integration lies in the open interval. -/
private lemma ae_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict (Set.uIoc 0 (2 * π))), θ ∈ Ioo (0:ℝ) (2 * π) := by
  rw [show Set.uIoc (0:ℝ) (2 * π) = Ioc 0 (2 * π) from uIoc_of_le (by positivity)]
  have h₁ : ∀ᵐ θ ∂(volume.restrict (Ioc (0:ℝ) (2 * π))), θ ∈ Ioc (0:ℝ) (2 * π) :=
    ae_restrict_mem measurableSet_Ioc
  have h₂ : ∀ᵐ (θ : ℝ) ∂(volume.restrict (Ioc (0:ℝ) (2 * π))), θ ≠ 2 * π := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp only [ne_eq, not_not, ofPred_eq_eq_singleton]
    exact measure_singleton _
  filter_upwards [h₁, h₂] with θ hθ h2
  exact ⟨hθ.1, lt_of_le_of_ne hθ.2 h2⟩

/-- The rotated singular integrand is interval integrable. -/
private lemma intervalIntegrable_shifted {a : ℂ} {r : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun θ ↦ ‖circleMap 0 r (θ + Complex.arg a) - a‖ ^ (-(2:ℝ)⁻¹))
      volume 0 (2 * π) := by
  apply IntervalIntegrable.mono_fun (intervalIntegrable_majorant hr)
  · apply Measurable.aestronglyMeasurable
    have h₁ : (fun θ ↦ ‖circleMap 0 r (θ + Complex.arg a) - a‖ ^ (-(2:ℝ)⁻¹))
        = fun θ ↦ (√(‖circleMap 0 r (θ + Complex.arg a) - a‖))⁻¹ := by
      funext θ
      rw [Real.rpow_neg (norm_nonneg _), show ((2:ℝ)⁻¹ : ℝ) = 1 / 2 by norm_num,
        ← Real.sqrt_eq_rpow]
    rw [h₁]
    apply Measurable.inv
    apply Continuous.measurable
    fun_prop
  · filter_upwards [ae_mem_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg
        (Real.rpow_nonneg (mul_nonneg (by positivity) hθ.1.le) _)
        (Real.rpow_nonneg (mul_nonneg (by positivity) (by linarith [hθ.2])) _))]
    exact rpow_norm_circleMap_le hr hθ

/-- Shifting the argument of a `2π`-periodic function preserves interval integrability over one
full period. -/
private lemma intervalIntegrable_comp_add_of_periodic {F : ℝ → ℝ}
    (hper : Function.Periodic F (2 * π)) (hF : IntervalIntegrable F volume 0 (2 * π)) (η : ℝ) :
    IntervalIntegrable (fun θ ↦ F (θ + η)) volume 0 (2 * π) := by
  have h₁ := hper.intervalIntegrable₀ (by positivity) hF η (2 * π + η)
  have h₂ := h₁.comp_add_right η
  simpa using h₂

/-- **C2, integrability**: the singular integrand `‖· - a‖ ^ (-2⁻¹)` is circle integrable, for
every center `a` and radius `r`. -/
theorem Real.circleIntegrable_norm_sub_rpow (a : ℂ) (r : ℝ) :
    CircleIntegrable (‖· - a‖ ^ (-(2:ℝ)⁻¹)) 0 r := by
  -- The case of positive radius
  have main : ∀ s : ℝ, 0 < s → CircleIntegrable (‖· - a‖ ^ (-(2:ℝ)⁻¹)) 0 s := by
    intro s hs
    have hper : Function.Periodic
        (fun θ ↦ ‖circleMap 0 s (θ + Complex.arg a) - a‖ ^ (-(2:ℝ)⁻¹)) (2 * π) := by
      intro θ
      simp only [show ∀ x : ℝ, x + 2 * π + Complex.arg a = x + Complex.arg a + 2 * π from
        fun x ↦ by ring, periodic_circleMap 0 s (θ + Complex.arg a)]
    have h₁ := intervalIntegrable_comp_add_of_periodic hper (intervalIntegrable_shifted hs)
      (-Complex.arg a)
    simpa [CircleIntegrable] using h₁
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · -- Negative radius: the parametrization is an angle-shift of the one with radius `-r`
    have hmap : ∀ θ : ℝ, circleMap 0 r θ = circleMap 0 (-r) (θ + π) := by
      intro θ
      simp only [circleMap, zero_add]
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    have hper : Function.Periodic (fun θ ↦ ‖circleMap 0 (-r) θ - a‖ ^ (-(2:ℝ)⁻¹)) (2 * π) :=
      fun θ ↦ by simp [periodic_circleMap 0 (-r) θ]
    have h₁ := intervalIntegrable_comp_add_of_periodic hper (main (-r) (by linarith)) π
    have h₂ : (fun θ ↦ ‖circleMap 0 r θ - a‖ ^ (-(2:ℝ)⁻¹))
        = fun θ ↦ ‖circleMap 0 (-r) (θ + π) - a‖ ^ (-(2:ℝ)⁻¹) := by
      funext θ
      rw [hmap θ]
    simpa [CircleIntegrable, h₂] using h₁
  · -- Zero radius: continuity on the degenerate sphere is trivial
    apply ContinuousOn.circleIntegrable'
    rw [abs_zero, Metric.sphere_zero]
    exact continuousOn_singleton _ _
  · exact main r hr

/-- **C2, uniform circle-average bound**: uniformly in `a : ℂ`, the circle average of
`‖· - a‖ ^ (-2⁻¹)` over the circle of radius `r > 0` is bounded by `4 * r ^ (-2⁻¹)`. -/
theorem Real.circleAverage_norm_sub_rpow_le {a : ℂ} {r : ℝ} (hr : 0 < r) :
    circleAverage (‖· - a‖ ^ (-(2:ℝ)⁻¹)) 0 r ≤ 4 * r ^ (-(2:ℝ)⁻¹) := by
  rw [circleAverage_eq_integral_add (Complex.arg a)]
  have hle : (∫ θ in (0:ℝ)..2 * π, ‖circleMap 0 r (θ + Complex.arg a) - a‖ ^ (-(2:ℝ)⁻¹))
      ≤ ∫ θ in (0:ℝ)..2 * π, ((r / (2 * π) * θ) ^ (-(2:ℝ)⁻¹)
        + (r / (2 * π) * (2 * π - θ)) ^ (-(2:ℝ)⁻¹)) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by positivity)
      (intervalIntegrable_shifted hr) (intervalIntegrable_majorant hr)
    exact fun θ hθ ↦ rpow_norm_circleMap_le hr hθ
  calc (2 * π)⁻¹ • ∫ θ in (0:ℝ)..2 * π, ‖circleMap 0 r (θ + Complex.arg a) - a‖ ^ (-(2:ℝ)⁻¹)
      ≤ (2 * π)⁻¹ * (8 * π * r ^ (-(2:ℝ)⁻¹)) := by
        rw [smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (le_trans hle (le_of_eq (integral_majorant hr)))
          (by positivity)
    _ = 4 * r ^ (-(2:ℝ)⁻¹) := by
        field_simp
        ring
