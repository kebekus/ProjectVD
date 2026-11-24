/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Circle Averages of Negative Powers of the Distance to a Point — LLD work package C2

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §5. The companion work package C1 (Jensen's inequality
for circle averages of `log⁺`) lives in `VD/MathlibSubmitted/JensenInequality.lean`.

This file shows that for `-1 < p ≤ 0`, the circle average of `‖· - a‖ ^ p` over a circle of radius
`r` is bounded by `|r| ^ p / (p + 1)`, **uniformly in `a : ℂ`**. The average of `‖· - a‖⁻¹`, in
contrast, is *not* uniformly bounded. This is why the two-radius estimate for the Lemma on the
Logarithmic Derivative uses the exponent-`1/2` trick: for `p = -2⁻¹` the bound reads
`2 * |r| ^ (-2⁻¹)`.

## Main results

- `circleIntegrable_iff_intervalIntegrable_add`: circle integrability does not change when shifting
  the angle.
- `circleIntegrable_norm_sub_const_rpow`: `‖· - a‖ ^ p` is circle integrable for `-1 < p`.
- `circleAverage_norm_sub_const_rpow_le`: the uniform bound described above.

## Implementation notes

The chord bound that this file builds on, `mul_abs_sin_le_norm_circleMap_zero_sub`, is in Mathlib
(merged as PR #43958). See the upstreaming notes below for where the material of this file belongs
in Mathlib.

The proofs rotate the circle by `arg (a - c)` and combine the chord bound
`mul_abs_sin_le_norm_circleMap_zero_sub` with Jordan's inequality `Real.mul_le_sin`. This majorizes
the integrand on `(0, 2 * π)` by `(r / π * min θ (2 * π - θ)) ^ p`. The majorant is a power
function on each half of the interval, so its integral is computed exactly. The resulting bound is
an equality for `p = 0`.

`circleIntegrable_norm_sub_const_rpow` is tagged `@[fun_prop]`. To apply it, `fun_prop` needs a
discharger for the hypothesis `-1 < p`, as in `fun_prop (disch := norm_num)`.
-/

@[expose] public section

/-
# Upstreaming notes

The chord lemmas that this file builds on have been merged into Mathlib as PR #43958. What is left
here is the second, dependent PR, described below. It was checked against the Mathlib revision
pinned in `lake-manifest.json` (`e62b985f`, 2026-11-24).

## Addition to `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`

`circleIntegrable_iff_intervalIntegrable_add` is the integrability counterpart of
`circleAverage_eq_integral_add` in `Mathlib/MeasureTheory/Integral/CircleAverage.lean`. It goes
directly before `circleIntegrable_neg_radius`. The target file declares `E` in its `variable`
block, so the binders `{E : Type*} [NormedAddCommGroup E]` are dropped there. Nothing else changes;
statement and proof were type-checked in the context of the target file.

The existing proof of `circleIntegrable_neg_radius` runs the same argument for the angle `π`. With
the new lemma in front of it, that proof can be shortened to

    rw [circleIntegrable_iff_intervalIntegrable_add (R := R) π, circleIntegrable_def]
    simp only [circleMap_neg_radius]

This is optional, but it shows that the new lemma is the statement behind the existing proof.

## New file `Mathlib/Analysis/SpecialFunctions/Integrals/CircleAverageRpow.lean`

Everything else goes into a new file next to `PosLog.lean`. It cannot go into
`Mathlib/MeasureTheory/Integral/CircleAverage.lean` itself: that file imports neither
`integral_rpow` (`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`) nor
`intervalIntegrable_rpow'` (`Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean`) nor
`Real.mul_le_sin` (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`), and it should
stay light. Appending to `PosLog.lean` would work but mixes themes and pulls in its heavy
harmonic-function imports for no reason. The new file needs the module-system header

    module

    public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
    public import Mathlib.MeasureTheory.Integral.CircleAverage

    public section

and receives the chord bound `mul_abs_sin_le_norm_circleMap_zero_sub` transitively through
`CircleAverage.lean`, `CircleIntegral.lean` and `CircleMap.lean`. The file's name is a suggestion;
any name matching the file's theme works.

Contents:
- `circleIntegrable_norm_sub_const_rpow` complements `circleIntegrable_sub_zpow_iff` in
  `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`, which covers integer powers of `· - a`.
  Mathlib has no `rpow` version yet. Its docstring points to `circleIntegrable_sub_zpow_iff`; a
  pointer in the other direction is optional.
- `circleAverage_norm_sub_const_rpow_le` has no Mathlib counterpart. Its docstring says that the
  bound is uniform in the center and in `a`, since that is the whole point, and that it is an
  equality for `p = 0`.
- The private helpers (`norm_circleMap_sub_rpow_le` and the four majorant lemmas) go along
  unchanged and stay private.
- In the module docstring, drop ` — LLD work package C2` from the title, the paragraph starting
  with "See `VD/LLD/PLAN-LogarithmicDerivative.md`", the last sentence of the paragraph after it
  (on the Lemma on the Logarithmic Derivative), the entry for
  `circleIntegrable_iff_intervalIntegrable_add` in the list of main results, and the first
  paragraph of the implementation notes. The rest goes along unchanged.

Where the material ends up:

| Declaration                                   | Mathlib target        | Visibility |
| --------------------------------------------- | --------------------- | ---------- |
| `circleIntegrable_iff_intervalIntegrable_add` | `CircleIntegral.lean` | public     |
| `norm_circleMap_sub_rpow_le`, majorant lemmas | new file              | private    |
| `circleIntegrable_norm_sub_const_rpow`        | new file              | public     |
| `circleAverage_norm_sub_const_rpow_le`        | new file              | public     |
-/

open intervalIntegral MeasureTheory Real Set

/-!
## Rotation Invariance of Circle Integrability
-/

/-- Circle integrability does not change when shifting the angle. See
`Real.circleAverage_eq_integral_add` for the analogous statement about circle averages. -/
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

/-- If `-1 < p`, then `‖· - a‖ ^ p` is circle integrable, for every center, radius and point `a`.
See `circleIntegrable_sub_zpow_iff` for integer powers of `· - a`. -/
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
is bounded by `|r| ^ p / (p + 1)`, uniformly in the center and in `a`. For `p = 0`, the bound is
an equality. -/
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
