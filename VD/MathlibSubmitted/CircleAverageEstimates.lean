/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Circle Averages of Negative Powers of the Distance to a Point

For a point `a : ℂ` and a real exponent `p`, this file studies the function `‖· - a‖ ^ p` on
circles in the complex plane. If `p` is negative and `a` lies on the circle, then the function has
a singularity there. The results of this file show that the singularity is harmless as long as
`-1 < p`.

## Main results

- `circleIntegrable_norm_sub_const_rpow`: if `-1 < p`, then `‖· - a‖ ^ p` is circle integrable,
  for every circle and every point `a`.
- `circleAverage_norm_sub_const_rpow_le`: if `-1 < p ≤ 0`, then the circle average of
  `‖· - a‖ ^ p` over a circle of radius `r ≠ 0` is at most `|r| ^ p / (p + 1)`.

The bound for the circle average depends neither on the center of the circle nor on `a`. In
particular, it does not deteriorate when `a` approaches the circle. This is what makes the bound
useful: it estimates circle averages of functions with finitely many singularities of this type,
no matter where the singularities are.

The assumption `-1 < p` is necessary. If `a` lies on a circle of nonzero radius, then `‖· - a‖⁻¹`
is not circle integrable (compare `circleIntegrable_sub_inv_iff`), and the circle averages of
`‖· - a‖⁻¹` are unbounded as `a` approaches the circle.

## Implementation notes

The proofs rotate the circle by `arg (a - c)`, so that the point of the circle that is closest to
`a` sits at the angle zero. The chord bound `mul_abs_sin_le_norm_circleMap_zero_sub` and Jordan's
inequality `Real.mul_le_sin` then majorize the integrand on `(0, 2 * π)` by
`(r / π * min θ (2 * π - θ)) ^ p`. The majorant is a power function on each half of the interval,
so its integral is computed exactly. The resulting bound is an equality for `p = 0`.

`circleIntegrable_norm_sub_const_rpow` is tagged `@[fun_prop]`. To apply it, `fun_prop` needs a
discharger for the hypothesis `-1 < p`, as in `fun_prop (disch := norm_num)`.
-/

@[expose] public section

/-
# Upstreaming plan

Project context: this file is work package C2 of the Lemma on the Logarithmic Derivative, see
`VD/LLD/PLAN-LogarithmicDerivative.md`, §5. Its consumer is the exponent-`1/2` trick
`circleAverage_posLog_norm_le_of_le_add_sum_inv_norm_sub` in `VD/LLD/LogDerivEstimates.lean`. The
companion work package C1 (Jensen's inequality for circle averages of `log⁺`) lives in
`VD/MathlibSubmitted/JensenInequality.lean`.

Status: ready for submission as one PR that touches two Mathlib files. The material depends on
Mathlib master only; the chord lemmas that it builds on were merged as PR #43958. It was checked
against the Mathlib revision pinned in `lake-manifest.json` (`e62b985f`, 2026-11-24). On that
day, no open Mathlib PR overlapped with it, and none of the project's open PRs (#43859, #43985,
#44428, #44629, #45423, #46392) touched the two target files.

## Step 1: add one lemma to `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`

`circleIntegrable_iff_intervalIntegrable_add` is the integrability counterpart of
`circleAverage_eq_integral_add` in `Mathlib/MeasureTheory/Integral/CircleAverage.lean`. It goes
directly before `circleIntegrable_neg_radius`, with its docstring. The target file declares `E`
in its `variable` block, so the binders `{E : Type*} [NormedAddCommGroup E]` are dropped there.
Nothing else changes; statement and proof were type-checked in the context of the target file.

The existing proof of `circleIntegrable_neg_radius` runs the same argument for the angle `π`. With
the new lemma in front of it, that proof can be shortened to

    rw [circleIntegrable_iff_intervalIntegrable_add (R := R) π, circleIntegrable_def]
    simp only [circleMap_neg_radius]

This is optional. It shows reviewers that the new lemma is the statement behind an existing proof,
but it also widens the diff; offer it in the PR description and apply it only on request.

## Step 2: create `Mathlib/Analysis/SpecialFunctions/Integrals/CircleAverageRpow.lean`

Everything from the line `variable {a c : ℂ} {r p θ : ℝ}` to the end of this file goes into the
new file, unchanged. The private helpers stay private. The new file starts with the copyright
header, then

    module

    public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
    public import Mathlib.MeasureTheory.Integral.CircleAverage

then the module docstring of this file, unchanged, then

    public section

    open intervalIntegral MeasureTheory Real Set

Note `public section` instead of this project's `@[expose] public section`. A copy in this form
compiles under Mathlib's linter set. Register the new file in `Mathlib.lean` with
`lake exe mk_all`.

Why this location. `Mathlib/Analysis/SpecialFunctions/Integrals/` holds computations and
estimates of integrals of specific functions, and its file `PosLog.lean` already treats circle
averages of `log ‖· - a‖`. The alternatives are worse:
- `Mathlib/MeasureTheory/Integral/CircleAverage.lean` holds the general theory and should stay
  light. It imports neither `integral_rpow`
  (`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`) nor `intervalIntegrable_rpow'`
  (`Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean`) nor `Real.mul_le_sin`
  (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`).
- Appending to `Mathlib/Analysis/SpecialFunctions/Integrals/PosLog.lean` mixes themes: that file
  is about `log⁺`, and it imports the theory of harmonic functions, which is not needed here.
- Splitting the material into `Integrability/…` and `Integrals/…`, as Mathlib does for `Log` and
  `PosLog`, does not work well: both main results rest on the same private majorant lemmas, which
  would have to become public.

The file name is a suggestion. Reviewers may prefer another one; nothing depends on it.

## Step 3: after the merge

- Delete this file and remove `VD.LLD.CircleAverageEstimates` from `VD.lean`.
- In `VD/LLD/LogDerivEstimates.lean`, replace the import of this file by
  `Mathlib.Analysis.SpecialFunctions.Integrals.CircleAverageRpow`.
- Mark row 7 of the upstreaming table in `VD/LLD/PLAN-LogarithmicDerivative.md` as merged.

## Where the material ends up

| Declaration                                   | Mathlib target        | Visibility |
| --------------------------------------------- | --------------------- | ---------- |
| `circleIntegrable_iff_intervalIntegrable_add` | `CircleIntegral.lean` | public     |
| `norm_circleMap_sub_rpow_le`, majorant lemmas | new file              | private    |
| `circleIntegrable_norm_sub_const_rpow`        | new file              | public     |
| `circleAverage_norm_sub_const_rpow_le`        | new file              | public     |
-/

open intervalIntegral MeasureTheory Real Set

-- The following lemma belongs in `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`; see step 1
-- of the upstreaming plan.

/-- Circle integrability can be checked after shifting the angle: a function `f` is circle
integrable if and only if `θ ↦ f (circleMap c R (θ + η))` is interval integrable over one period,
for any angle `η`. See `Real.circleAverage_eq_integral_add` for the analogous statement about
circle averages. -/
theorem circleIntegrable_iff_intervalIntegrable_add {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    {c : ℂ} {R : ℝ} (η : ℝ) :
    CircleIntegrable f c R ↔
      IntervalIntegrable (fun θ ↦ f (circleMap c R (θ + η))) volume 0 (2 * π) := by
  rw [IntervalIntegrable.comp_add_right_iff (f := fun θ ↦ f (circleMap c R θ)), zero_add, add_comm]
  simpa using! ((periodic_circleMap c R).comp f).intervalIntegrable_iff (t₁ := 0) (t₂ := η)

variable {a c : ℂ} {r p θ : ℝ}

/-!
## The Majorant
-/

-- Pointwise majorization of the rotated integrand, by the chord bound and Jordan's inequality.
private lemma norm_circleMap_sub_rpow_le (hr : 0 < r) (hp : p ≤ 0) (hθ : θ ∈ Ioo 0 (2 * π)) :
    ‖circleMap c r (θ + (a - c).arg) - a‖ ^ p ≤ (r / π * min θ (2 * π - θ)) ^ p := by
  have hmin : 0 < min θ (2 * π - θ) := lt_min hθ.1 (sub_pos.2 hθ.2)
  -- The chord bound
  have chord := mul_abs_sin_le_norm_circleMap_zero_sub r (θ + (a - c).arg) (a - c)
  rw [add_sub_cancel_right, ← circleMap_sub_center c, sub_sub_sub_cancel_right] at chord
  -- Jordan's inequality
  have jordan {x : ℝ} (h₀ : 0 ≤ x) (hx : x ≤ π) : r / π * x ≤ r * |sin (x / 2)| :=
    calc r / π * x = r * (2 / π * (x / 2)) := by ring
      _ ≤ r * |sin (x / 2)| := by
        gcongr
        exact (mul_le_sin (by positivity) (by linarith)).trans (le_abs_self _)
  refine rpow_le_rpow_of_nonpos (by positivity) (le_trans ?_ chord) hp
  -- Apply Jordan's inequality to the angular distance from the nearer end of the interval
  obtain h | h := le_total θ π
  · rw [min_eq_left (by linarith)]
    exact jordan hθ.1.le h
  · rw [min_eq_right (by linarith), show θ / 2 = π - (2 * π - θ) / 2 by ring, sin_pi_sub]
    exact jordan (by linarith [hθ.2]) (by linarith)

-- On the left half of the interval, the majorant is a power function.
private lemma majorant_eqOn :
    EqOn (fun θ ↦ (r / π * min θ (2 * π - θ)) ^ p) (fun θ ↦ (r / π * θ) ^ p) (Icc 0 π) :=
  fun θ hθ ↦ by simp only [min_eq_left (by linarith [hθ.2] : θ ≤ 2 * π - θ)]

private lemma intervalIntegrable_majorant_left (hr : 0 < r) (hp : -1 < p) :
    IntervalIntegrable (fun θ ↦ (r / π * min θ (2 * π - θ)) ^ p) volume 0 π := by
  rw [intervalIntegrable_congr (majorant_eqOn.mono (uIoc_of_le pi_pos.le ▸ Ioc_subset_Icc_self))]
  simpa [div_div_cancel₀ hr.ne'] using
    (intervalIntegrable_rpow' hp (a := 0) (b := r)).comp_mul_left (c := r / π)

-- The majorant is symmetric about `π`: the substitution `θ ↦ 2 * π - θ` swaps the two halves.
private lemma intervalIntegrable_majorant_right (hr : 0 < r) (hp : -1 < p) :
    IntervalIntegrable (fun θ ↦ (r / π * min θ (2 * π - θ)) ^ p) volume π (2 * π) := by
  simpa [min_comm, two_mul] using
    ((intervalIntegrable_majorant_left hr hp).comp_sub_left (2 * π)).symm

private lemma integral_majorant (hr : 0 < r) (hp : -1 < p) :
    ∫ θ in 0..2 * π, (r / π * min θ (2 * π - θ)) ^ p = 2 * π * (r ^ p / (p + 1)) := by
  -- On `[0, π]`, the substitution `x = r / π * θ` computes the integral
  have h₁ : ∫ θ in 0..π, (r / π * min θ (2 * π - θ)) ^ p = π * (r ^ p / (p + 1)) := by
    rw [integral_congr (majorant_eqOn.mono (uIcc_of_le pi_pos.le).subset),
      integral_comp_mul_left (· ^ p) (by positivity), mul_zero, div_mul_cancel₀ r (by positivity),
      integral_rpow (.inl hp), zero_rpow (by linarith), sub_zero, rpow_add_one hr.ne', smul_eq_mul]
    field
  -- The substitution `θ ↦ 2 * π - θ` reduces the integral over `[π, 2 * π]` to that over `[0, π]`
  have h₂ : ∫ θ in π..2 * π, (r / π * min θ (2 * π - θ)) ^ p = π * (r ^ p / (p + 1)) := by
    rw [← h₁]
    simpa [min_comm, two_mul] using (integral_comp_sub_left
      (fun θ ↦ (r / π * min θ (2 * π - θ)) ^ p) (2 * π) (a := 0) (b := π)).symm
  rw [← integral_add_adjacent_intervals (intervalIntegrable_majorant_left hr hp)
    (intervalIntegrable_majorant_right hr hp), h₁, h₂]
  ring

/-!
## Main Results
-/

/-- If `-1 < p`, then the function `‖· - a‖ ^ p` is circle integrable, for every center `c`, every
radius `r` and every point `a`. The point `a` may lie on the circle, where the function has a
singularity if `p` is negative. See `circleIntegrable_sub_zpow_iff` for integer powers of
`· - a`. -/
@[fun_prop]
theorem circleIntegrable_norm_sub_const_rpow (hp : -1 < p) :
    CircleIntegrable (‖· - a‖ ^ p) c r := by
  wlog hr : 0 < r generalizing r
  · obtain rfl | hr := (not_lt.1 hr).eq_or_lt
    · exact circleIntegrable_zero_radius
    · exact circleIntegrable_neg_radius.1 (this (neg_pos.2 hr))
  obtain hp₀ | hp₀ := lt_or_ge 0 p
  · exact (Continuous.rpow_const (by fun_prop) fun _ ↦ .inr hp₀.le).continuousOn.circleIntegrable'
  -- Rotate the circle by `arg (a - c)` and compare with the majorant
  rw [circleIntegrable_iff_intervalIntegrable_add (a - c).arg]
  refine ((intervalIntegrable_majorant_left hr hp).trans (intervalIntegrable_majorant_right hr hp))
    |>.mono_fun' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  rw [uIoc_of_le two_pi_pos.le, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ using
    (norm_of_nonneg (by positivity)).trans_le (norm_circleMap_sub_rpow_le hr hp₀ hθ)

/-- If `-1 < p ≤ 0`, then the circle average of `‖· - a‖ ^ p` over a circle of nonzero radius `r`
is at most `|r| ^ p / (p + 1)`. The bound depends neither on the center `c` nor on the point `a`,
which may lie on the circle or arbitrarily close to it. For `p = 0`, the bound is an equality. -/
theorem circleAverage_norm_sub_const_rpow_le (hr : r ≠ 0) (hp₁ : -1 < p) (hp₂ : p ≤ 0) :
    circleAverage (‖· - a‖ ^ p) c r ≤ |r| ^ p / (p + 1) := by
  have hr' : 0 < |r| := abs_pos.2 hr
  -- Rotate the circle by `arg (a - c)` and compare with the integral of the majorant
  rw [← circleAverage_abs_radius, circleAverage_eq_integral_add (a - c).arg, smul_eq_mul,
    inv_mul_le_iff₀ two_pi_pos, ← integral_majorant hr' hp₁]
  exact integral_mono_on_of_le_Ioo two_pi_pos.le
    ((circleIntegrable_iff_intervalIntegrable_add _).1 (circleIntegrable_norm_sub_const_rpow hp₁))
    ((intervalIntegrable_majorant_left hr' hp₁).trans (intervalIntegrable_majorant_right hr' hp₁))
    fun _ ↦ norm_circleMap_sub_rpow_le hr' hp₂
