/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Circle Averages of Negative Powers of the Distance to a Point — LLD work package C2

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §5. The companion work package C1 (Jensen's inequality
for circle averages of `log⁺`) lives in `VD/MathlibSubmitted/JensenInequality.lean`.

This file shows that for `-1 < p ≤ 0`, the circle average of `‖· - a‖ ^ p` over a circle of radius
`r` is bounded by `2 / (p + 1) * |r| ^ p`, **uniformly in `a : ℂ`**. For `p = -2⁻¹` the bound reads
`4 * |r| ^ (-2⁻¹)`; this uniformity is why the two-radius estimate for the Lemma on the Logarithmic
Derivative uses the exponent-`1/2` trick: the average of `‖· - a‖⁻¹` is *not* uniformly bounded.

## Main results

- `norm_circleMap_zero_sub_sq`, `norm_circleMap_zero_sub_sq'`: the law of cosines for the chord from
  a point of the circle `circleMap 0 r` to an arbitrary point `a`, in cosine and in half-angle form.
- `mul_abs_sin_le_norm_circleMap_zero_sub`: the sharp universal lower bound
  `r * |sin ((θ - arg a) / 2)| ≤ ‖circleMap 0 r θ - a‖`.
- `circleIntegrable_norm_sub_const_rpow`: `‖· - a‖ ^ p` is circle integrable for `-1 < p`.
- `circleAverage_norm_sub_const_rpow_le`: the uniform bound described above.

## Implementation notes

The chord lemmas need no measure theory. See the upstreaming notes below for where the material of
this file belongs in Mathlib.

For the average, rotate the circle by `arg a` and combine the chord bound with the Jordan inequality
`Real.mul_le_sin`. This majorizes the integrand by `(r/(2π) * θ) ^ p + (r/(2π) * (2π - θ)) ^ p`,
whose integral is computed exactly.
-/

/-
# Upstreaming notes

The material of this file is meant to go to Mathlib in two PRs. The second depends on the first.
Everything below was checked against the Mathlib revision pinned in `lake-manifest.json`
(`f61f3ed7`, 2026-09-17). Mathlib itself was *not* modified: the rewritten Mathlib proofs quoted
below were compiled as standalone copies in a scratch file that imports this file. In that test,
the private Mathlib lemma `circleAverage_log_norm_sub_const₁_integral` was replaced by a hypothesis
of the same statement.

## PR 1: chord lemmas in `Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean`

Move `norm_circleMap_zero_sub_sq`, `norm_circleMap_zero_sub_sq'` and
`mul_abs_sin_le_norm_circleMap_zero_sub` verbatim to `CircleMap.lean`, directly after
`circleMap_zero_re` (which the first proof uses) and `circleMap_zero_im`. They need no measure
theory and compile with only `import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap`. This was
checked in classic mode; recheck under the module system, because the proofs use
`linear_combination`, `nlinarith` and `positivity`.

The first lemma is not new mathematics in Mathlib, only a new *statement*: its proof is lifted from
the inline `have h_cos_law` in `JensenFormula.lean`, with the hypothesis `‖ρ‖ = R` removed (it was
only used to rename `‖ρ‖` to `R`). The existing lemma `Complex.norm_exp_I_mul_ofReal_sub_one` in
`Mathlib/Analysis/Complex/Trigonometric.lean` is the special case `r = 1`, `a = 1` of the
half-angle form. It sits below `CircleMap.lean` in the import hierarchy and therefore stays where it
is, but the docstrings should point to each other.

PR 1 should also simplify the two Mathlib proofs that currently contain their own copies of the law
of cosines. Together they shrink from about 60 lines to about 20.

### `Mathlib/Analysis/Complex/JensenFormula.lean`

The private lemma `const_mul_norm_sub_circleMap_le_norm_sub_circleMap` (15 lines) proves the law of
cosines inline, then needs `nlinarith` with six hints to compare the chords of radius `r` and `R`.
In half-angle form, with `t = sin ((θ - arg ρ) / 2) ^ 2`, the squared inequality becomes
`4 * r₀ * R ^ 2 * t ≤ R * (r - R) ^ 2 + 4 * r * R ^ 2 * t`, which is immediate from `r₀ ≤ r`. The
lemma becomes:

    private lemma const_mul_norm_sub_circleMap_le_norm_sub_circleMap {r₀ r R : ℝ} {ρ : ℂ}
        (hρ : ‖ρ‖ = R) (hr₀ : 0 < r₀) (hR : 0 < R) (hr₀r : r₀ ≤ r) (θ : ℝ) :
        sqrt (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ≤ ‖circleMap 0 r θ - ρ‖ := by
      have : (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ^ 2 ≤ ‖circleMap 0 r θ - ρ‖ ^ 2 := by
        rw [norm_circleMap_zero_sub_sq', norm_circleMap_zero_sub_sq', hρ, div_mul_eq_mul_div,
          div_le_iff₀ hR]
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg R) (sq_nonneg (sin ((θ - ρ.arg) / 2))))
          (sub_nonneg.2 hr₀r), mul_nonneg hR.le (sq_nonneg (r - R))]
      grw [← sqrt_sq (norm_nonneg _), ← sqrt_mul (by positivity), this, sqrt_sq (norm_nonneg _)]

The hypothesis `hrR : r ≤ R` is no longer needed and should be dropped. Its only caller,
`norm_herglotzLogIntegrand_circleMap_le`, then omits `hrR` from the call. The caller keeps `hrR` in
its own signature, because it uses it elsewhere. A more conservative alternative keeps the proof as
it is and only replaces the seven-line `h_cos_law` by `rw [norm_circleMap_zero_sub_sq, hρ]`.

### `Mathlib/Analysis/SpecialFunctions/Integrals/PosLogEqCircleAverage.lean`

The proof of `circleAverage_log_norm_sub_const₁` (45 lines) first rotates the circle to move `a` to
`1`. It does this by hand, with `circleMap_zero_mul`, `Function.Periodic.intervalIntegral_add_eq`
and `integral_comp_add_left`. It then computes `normSq (circleMap 0 1 x - 1) = 4 * sin (x / 2) ^ 2`
in a 16-line `calc`. The rotation is exactly `Real.circleAverage_eq_integral_add` (in
`CircleAverage.lean`, which the file already imports), and the computation is the half-angle form
at `r = ‖a‖ = 1`. The theorem becomes:

    theorem circleAverage_log_norm_sub_const₁ (h : ‖a‖ = 1) :
        circleAverage (log ‖· - a‖) 0 1 = 0 := by
      -- Rotate by `arg a`. By the law of cosines,
      -- `‖circleMap 0 1 (x + arg a) - a‖ ^ 2 = 4 * sin (x / 2) ^ 2`.
      rw [circleAverage_eq_integral_add a.arg,
        integral_congr (g := fun x ↦ log (4 * sin (x / 2) ^ 2) / 2),
        circleAverage_log_norm_sub_const₁_integral, smul_zero]
      intro x _
      have := norm_circleMap_zero_sub_sq' 1 (x + a.arg) a
      norm_num [h] at this
      simp only [← this, log_pow]
      ring

The private lemma `circleAverage_log_norm_sub_const₁_integral` is unchanged. A more conservative
alternative keeps the rotation and only replaces the 16-line `calc` by
`Complex.normSq_eq_norm_sq _` followed by `simp [norm_circleMap_zero_sub_sq']`.

No other Mathlib file computes chord lengths of `circleMap` by hand, as far as a search for
`normSq (circleMap`, `cos (θ - … arg …)` and `sin (x / 2) ^ 2` shows.

## PR 2: new file `Mathlib/Analysis/SpecialFunctions/Integrals/CircleAverageRpow.lean`

Everything from the section "The Majorant" onwards goes into a new file next to
`PosLogEqCircleAverage.lean`. It cannot go into `Mathlib/MeasureTheory/Integral/CircleAverage.lean`
itself: that file does not import `integral_rpow` and `intervalIntegrable_rpow'` (from
`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`), and it should stay light. Appending to
`PosLogEqCircleAverage.lean` would work but mixes themes and pulls in its heavy harmonic-function
imports for no reason. The new file needs the module-system header

    module

    public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
    public import Mathlib.MeasureTheory.Integral.CircleAverage

    public section

and receives the chord lemmas of PR 1 transitively through `CircleAverage.lean`,
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
| `norm_circleMap_zero_sub_sq`                  | `…/Complex/CircleMap.lean`    | public     |
| `norm_circleMap_zero_sub_sq'`                 | `…/Complex/CircleMap.lean`    | public     |
| `mul_abs_sin_le_norm_circleMap_zero_sub`      | `…/Complex/CircleMap.lean`    | public     |
| `norm_circleMap_sub_eq`                       | new file, or `CircleMap.lean` | private    |
| majorant lemmas, `intervalIntegrable_shifted` | new file                      | private    |
| `circleIntegrable_norm_sub_const_rpow`        | new file                      | public     |
| `circleAverage_norm_sub_const_rpow_le`        | new file                      | public     |
-/

open Complex Filter MeasureTheory Real Set

variable {a c : ℂ} {r p θ : ℝ}

/-!
## Chord Lengths
-/

/-- Law of cosines for the chord from a point of the circle `circleMap 0 r` to an arbitrary point
`a`. -/
theorem norm_circleMap_zero_sub_sq (r θ : ℝ) (a : ℂ) :
    ‖circleMap 0 r θ - a‖ ^ 2 = r ^ 2 + ‖a‖ ^ 2 - 2 * r * ‖a‖ * Real.cos (θ - a.arg) := by
  rw [← ofReal_inj, ← normSq_eq_norm_sq, normSq_sub]
  suffices (circleMap 0 r θ * (starRingEnd ℂ) a).re = r * ‖a‖ * Real.cos (θ - a.arg) by
    simp [normSq_eq_norm_sq, -mul_re, this, mul_assoc]
  conv_lhs => rw [← norm_mul_exp_arg_mul_I a, ← circleMap_zero, conj_circleMap_zero,
    circleMap_zero_mul, circleMap_zero_re, ← sub_eq_add_neg]

/-- Law of cosines for the chord from a point of the circle `circleMap 0 r` to an arbitrary point
`a`, half-angle form. -/
theorem norm_circleMap_zero_sub_sq' (r θ : ℝ) (a : ℂ) :
    ‖circleMap 0 r θ - a‖ ^ 2
      = (r - ‖a‖) ^ 2 + 4 * r * ‖a‖ * Real.sin ((θ - a.arg) / 2) ^ 2 := by
  have h := Real.sin_sq_eq_half_sub ((θ - a.arg) / 2)
  rw [show 2 * ((θ - a.arg) / 2) = θ - a.arg by ring] at h
  rw [norm_circleMap_zero_sub_sq]
  linear_combination (-(4 * r * ‖a‖)) * h

/-- Points of the circle `circleMap 0 r` keep distance at least `r * |sin ((θ - arg a) / 2)|` from
any point `a`. The bound is sharp: equality holds for `a = 0` and `θ = π`. -/
theorem mul_abs_sin_le_norm_circleMap_zero_sub (hr : 0 ≤ r) (θ : ℝ) (a : ℂ) :
    r * |Real.sin ((θ - a.arg) / 2)| ≤ ‖circleMap 0 r θ - a‖ := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [mul_pow, sq_abs, norm_circleMap_zero_sub_sq']
  nlinarith [mul_nonneg (sub_nonneg.2 (Real.sin_sq_le_one ((θ - a.arg) / 2)))
      (sq_nonneg (r - ‖a‖)),
    mul_nonneg (mul_nonneg (sq_nonneg (Real.sin ((θ - a.arg) / 2))) (norm_nonneg a))
      (by positivity : (0:ℝ) ≤ 2 * r + ‖a‖)]

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
