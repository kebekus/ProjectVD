/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage
import VD.MathlibSubmitted.ChordLength

/-!
# Circle Averages of Negative Powers of the Distance to a Point — LLD work package C2

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §5. The companion work package C1 (Jensen's inequality
for circle averages of `log⁺`) lives in `VD/MathlibSubmitted/JensenInequality.lean`.

This file shows that for `-1 < p ≤ 0`, the circle average of `‖· - a‖ ^ p` over a circle of radius
`r` is bounded by `2 / (p + 1) * |r| ^ p`, **uniformly in `a : ℂ`**. For `p = -2⁻¹` the bound reads
`4 * |r| ^ (-2⁻¹)`; this uniformity is why the two-radius estimate for the Lemma on the Logarithmic
Derivative uses the exponent-`1/2` trick: the average of `‖· - a‖⁻¹` is *not* uniformly bounded.

## Main results

- `circleIntegrable_norm_sub_const_rpow`: `‖· - a‖ ^ p` is circle integrable for `-1 < p`.
- `circleAverage_norm_sub_const_rpow_le`: the uniform bound described above.

## Implementation notes

The chord lemmas that this file builds on (`norm_circleMap_zero_sub_sq'` and
`mul_abs_sin_le_norm_circleMap_zero_sub`) have been submitted to Mathlib as PR #43958 and live in
`VD/MathlibSubmitted/ChordLength.lean`. See the upstreaming notes below for where the material of
this file belongs in Mathlib.

For the average, rotate the circle by `arg a` and combine the chord bound with the Jordan inequality
`Real.mul_le_sin`. This majorizes the integrand by `(r/(2π) * θ) ^ p + (r/(2π) * (2π - θ)) ^ p`,
whose integral is computed exactly.
-/

/-
# Upstreaming notes

The chord lemmas that this file builds on have been submitted to Mathlib as PR #43958; they now live
in `VD/MathlibSubmitted/ChordLength.lean`, which also records what else that PR changes. What is
left here is the second, dependent PR, described below. It was checked against the Mathlib revision
pinned in `lake-manifest.json` (`f61f3ed7`, 2026-09-17).

## New file `Mathlib/Analysis/SpecialFunctions/Integrals/CircleAverageRpow.lean`

Everything in this file goes into a new file next to `PosLog.lean`. It cannot go into
`Mathlib/MeasureTheory/Integral/CircleAverage.lean`
itself: that file does not import `integral_rpow` and `intervalIntegrable_rpow'` (from
`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`), and it should stay light. Appending to
`PosLog.lean` would work but mixes themes and pulls in its heavy harmonic-function imports for no
reason. The new file needs the module-system header

    module

    public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
    public import Mathlib.MeasureTheory.Integral.CircleAverage

    public section

and receives the chord lemmas of PR #43958 transitively through `CircleAverage.lean`,
`CircleIntegral.lean` and `CircleMap.lean`. The file's name is a suggestion; any name matching the
file's theme works.

Contents:
- `circleIntegrable_norm_sub_const_rpow` is the real-exponent counterpart of
  `circleIntegrable_sub_zpow_iff` in `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`, which
  covers integer exponents only. Mathlib has no `rpow` version yet. The docstrings should point to
  each other.
- `circleAverage_norm_sub_const_rpow_le` has no Mathlib counterpart. Its docstring should say that
  the bound is uniform in the center and in `a`, since that is the whole point.
- The private helpers (`div_mul_le_mul_abs_sin`, `rpow_norm_circleMap_le`, the three majorant
  lemmas, `intervalIntegrable_shifted`, `norm_circleMap_sub_eq`) go along unchanged and stay
  private. `div_mul_le_mul_abs_sin` is too specialised for
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`. `norm_circleMap_sub_eq` could
  instead become a public lemma next to `circleMap_sub_center` in `CircleMap.lean`. It must not be
  tagged `@[simp]`: at centre `0` its right-hand side matches its left-hand side, so `simp` loops.
- The module docstring should drop the references to the LLD project and keep the mathematical
  explanation. Mention that `fun_prop` needs a discharger for the hypothesis `-1 < p`, as in
  `fun_prop (disch := norm_num)`.

Where the material ends up:

| Declaration                                   | Mathlib target                | Visibility |
| --------------------------------------------- | ----------------------------- | ---------- |
| `norm_circleMap_sub_eq`                       | new file, or `CircleMap.lean` | private    |
| majorant lemmas, `intervalIntegrable_shifted` | new file                      | private    |
| `circleIntegrable_norm_sub_const_rpow`        | new file                      | public     |
| `circleAverage_norm_sub_const_rpow_le`        | new file                      | public     |
-/

open Complex Filter MeasureTheory Real Set

variable {a c : ℂ} {r p θ : ℝ}

/-!
## The Majorant
-/

-- Jordan's inequality, in the form needed for the majorant.
private lemma div_mul_le_mul_abs_sin (hr : 0 ≤ r) (h₁ : 0 ≤ θ) (h₂ : θ ≤ π) :
    r / (2 * π) * θ ≤ r * |Real.sin (θ / 2)| := by
  have h := Real.mul_le_sin (x := θ / 2) (by linarith) (by linarith)
  calc r / (2 * π) * θ ≤ r * (2 / π * (θ / 2)) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        field_simp
        nlinarith [mul_nonneg hr h₁, pi_pos]
    _ ≤ r * |Real.sin (θ / 2)| := by gcongr; exact h.trans (le_abs_self _)

-- Pointwise majorization of the rotated integrand.
private lemma rpow_norm_circleMap_le (hr : 0 < r) (hp : p ≤ 0) (hθ : θ ∈ Ioo 0 (2 * π)) :
    ‖circleMap 0 r (θ + a.arg) - a‖ ^ p
      ≤ (r / (2 * π) * θ) ^ p + (r / (2 * π) * (2 * π - θ)) ^ p := by
  obtain ⟨h₁, h₂⟩ := hθ
  have hlow := mul_abs_sin_le_norm_circleMap_zero_sub hr.le (θ + a.arg) a
  rw [add_sub_cancel_right] at hlow
  rcases le_total θ π with h | h
  · refine le_add_of_le_of_nonneg ?_ (rpow_nonneg (mul_nonneg (by positivity) (by linarith)) _)
    exact rpow_le_rpow_of_nonpos (by positivity)
      ((div_mul_le_mul_abs_sin hr.le h₁.le h).trans hlow) hp
  · rw [show θ / 2 = π - (2 * π - θ) / 2 by ring, Real.sin_pi_sub] at hlow
    refine le_add_of_nonneg_of_le (rpow_nonneg (by positivity) _) ?_
    exact rpow_le_rpow_of_nonpos (mul_pos (by positivity) (by linarith))
      ((div_mul_le_mul_abs_sin hr.le (by linarith) (by linarith)).trans hlow) hp

private lemma intervalIntegrable_majorant_left (hr : 0 < r) (hp : -1 < p) :
    IntervalIntegrable (fun θ : ℝ ↦ (r / (2 * π) * θ) ^ p) volume 0 (2 * π) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' hp (a := 0) (b := r)).comp_mul_left
    (c := r / (2 * π))
  simpa [show r / (r / (2 * π)) = 2 * π by field_simp] using h

private lemma intervalIntegrable_majorant_right (hr : 0 < r) (hp : -1 < p) :
    IntervalIntegrable (fun θ : ℝ ↦ (r / (2 * π) * (2 * π - θ)) ^ p) volume 0 (2 * π) := by
  simpa using ((intervalIntegrable_majorant_left hr hp).comp_sub_left (2 * π)).symm

private lemma integral_majorant (hr : 0 < r) (hp : -1 < p) :
    ∫ θ in (0:ℝ)..2 * π, ((r / (2 * π) * θ) ^ p + (r / (2 * π) * (2 * π - θ)) ^ p)
      = 4 * π / (p + 1) * r ^ p := by
  have hp' : 0 < p + 1 := by linarith
  have e : ∫ θ in (0:ℝ)..2 * π, (r / (2 * π) * (2 * π - θ)) ^ p
      = ∫ θ in (0:ℝ)..2 * π, (r / (2 * π) * θ) ^ p := by
    simpa using intervalIntegral.integral_comp_sub_left (a := 0) (b := 2 * π)
      (fun θ ↦ (r / (2 * π) * θ) ^ p) (2 * π)
  rw [intervalIntegral.integral_add (intervalIntegrable_majorant_left hr hp)
      (intervalIntegrable_majorant_right hr hp), e,
    intervalIntegral.integral_comp_mul_left (fun x ↦ x ^ p) (by positivity), mul_zero,
    show r / (2 * π) * (2 * π) = r by field_simp, integral_rpow (Or.inl hp),
    zero_rpow hp'.ne', sub_zero, smul_eq_mul, rpow_add hr, rpow_one]
  field_simp
  ring

-- The rotated integrand is interval integrable.
private lemma intervalIntegrable_shifted (hr : 0 < r) (hp₁ : -1 < p) (hp₂ : p ≤ 0) :
    IntervalIntegrable (fun θ ↦ ‖circleMap 0 r (θ + a.arg) - a‖ ^ p) volume 0 (2 * π) := by
  refine ((intervalIntegrable_majorant_left hr hp₁).add
    (intervalIntegrable_majorant_right hr hp₁)).mono_fun' ?_ ?_
  · have : Continuous fun θ ↦ ‖circleMap 0 r (θ + a.arg) - a‖ := by fun_prop
    exact (this.measurable.pow_const p).aestronglyMeasurable
  · rw [uIoc_of_le two_pi_pos.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc, EventuallyLE,
      ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with θ hθ
    rw [norm_of_nonneg (rpow_nonneg (norm_nonneg _) _)]
    exact rpow_norm_circleMap_le hr hp₂ hθ

/-!
## Main Results
-/

private lemma norm_circleMap_sub_eq (c a : ℂ) (r θ : ℝ) :
    ‖circleMap c r θ - a‖ = ‖circleMap 0 r θ - (a - c)‖ := by
  rw [← circleMap_sub_center c r θ]
  ring_nf

/-- If `-1 < p`, then `‖· - a‖ ^ p` is circle integrable, for every center, radius and point `a`. -/
@[fun_prop]
theorem circleIntegrable_norm_sub_const_rpow (hp : -1 < p) (r : ℝ) :
    CircleIntegrable (‖· - a‖ ^ p) c r := by
  rcases lt_or_ge 0 p with hp₀ | hp₀
  · exact (Continuous.rpow_const (by fun_prop) fun _ ↦ Or.inr hp₀.le).continuousOn.circleIntegrable'
  -- Positive radius: shift the angle by `arg (a - c)` and use periodicity
  have main {s : ℝ} (hs : 0 < s) : CircleIntegrable (‖· - a‖ ^ p) c s := by
    have hper : Function.Periodic (fun θ ↦ ‖circleMap 0 s θ - (a - c)‖ ^ p) (2 * π) :=
      fun θ ↦ by simp [periodic_circleMap 0 s θ]
    have h := (IntervalIntegrable.comp_add_right_iff
      (f := fun θ ↦ ‖circleMap 0 s θ - (a - c)‖ ^ p) (c := (a - c).arg) (a := 0) (b := 2 * π)).1
      (intervalIntegrable_shifted hs hp hp₀)
    rw [zero_add, add_comm (2 * π)] at h
    simpa [CircleIntegrable, norm_circleMap_sub_eq c a s]
      using (hper.intervalIntegrable_iff (t₂ := 0)).1 h
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · rw [← neg_neg r, circleIntegrable_neg_radius]
    exact main (neg_pos.2 hr)
  · simp
  · exact main hr

/-- If `-1 < p ≤ 0`, then the circle average of `‖· - a‖ ^ p` over a circle of nonzero radius `r`
is bounded by `2 / (p + 1) * |r| ^ p`, uniformly in the center and in `a`. -/
theorem circleAverage_norm_sub_const_rpow_le (hr : r ≠ 0) (hp₁ : -1 < p) (hp₂ : p ≤ 0) :
    circleAverage (‖· - a‖ ^ p) c r ≤ 2 / (p + 1) * |r| ^ p := by
  have hr' : 0 < |r| := abs_pos.2 hr
  rw [← circleAverage_abs_radius, circleAverage_eq_integral_add (a - c).arg, smul_eq_mul]
  simp only [norm_circleMap_sub_eq c a |r|]
  calc (2 * π)⁻¹ * ∫ θ in 0..2 * π, ‖circleMap 0 |r| (θ + (a - c).arg) - (a - c)‖ ^ p
      ≤ (2 * π)⁻¹ * (4 * π / (p + 1) * |r| ^ p) := by
        gcongr
        rw [← integral_majorant hr' hp₁]
        exact intervalIntegral.integral_mono_on_of_le_Ioo two_pi_pos.le
          (intervalIntegrable_shifted hr' hp₁ hp₂)
          ((intervalIntegrable_majorant_left hr' hp₁).add
            (intervalIntegrable_majorant_right hr' hp₁))
          fun θ hθ ↦ rpow_norm_circleMap_le hr' hp₂ hθ
    _ = 2 / (p + 1) * |r| ^ p := by
        field_simp
        ring
