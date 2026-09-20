/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Chord Lengths for `circleMap`

Submitted to Mathlib as PR #43958, "feat: simplify computations in complex analysis by extracting
frequently-used lemmas", https://github.com/leanprover-community/mathlib4/pull/43958.

Mathlib target: `Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean`, directly after
`circleMap_zero_re` and `circleMap_zero_im`. The declarations below are the submitted text,
verbatim.

## Main results

- `norm_circleMap_zero_sub_sq`, `norm_circleMap_zero_sub_sq'`: the law of cosines for the chord from
  a point of the circle `circleMap 0 r` to an arbitrary point `a`, in cosine and in half-angle form.
- `mul_abs_sin_le_norm_circleMap_zero_sub`: the sharp universal lower bound
  `r * |sin ((θ - arg a) / 2)| ≤ ‖circleMap 0 r θ - a‖`.

## Implementation notes

The lemmas need no measure theory. The first is not new mathematics in Mathlib, only a new
*statement*: its proof is lifted from the inline `have h_cos_law` in `JensenFormula.lean`, with the
hypothesis `‖ρ‖ = R` removed (it was only used to rename `‖ρ‖` to `R`). The existing lemma
`Complex.norm_exp_I_mul_ofReal_sub_one` in `Mathlib/Analysis/Complex/Trigonometric.lean` is the
special case `r = 1`, `a = 1` of the half-angle form. It sits below `CircleMap.lean` in the import
hierarchy and therefore stays where it is; the PR only adds cross-references between the docstrings.

Besides adding these three lemmas, the PR simplifies the two Mathlib proofs that carried their own
copies of the law of cosines: the private `const_mul_norm_sub_circleMap_le_norm_sub_circleMap` in
`Mathlib/Analysis/Complex/JensenFormula.lean`, whose hypothesis `hrR : r ≤ R` thereby becomes
superfluous and is dropped, and `circleAverage_log_norm_sub_const₁` in
`Mathlib/Analysis/SpecialFunctions/Integrals/PosLog.lean`. Together the two shrink from about 60
lines to about 20. Both changes are edits to Mathlib files and have no counterpart in this
directory.

Once the PR is merged, delete this file and remove the import from
`VD/LLD/CircleAverageEstimates.lean`, which then receives the lemmas transitively through
`Mathlib/MeasureTheory/Integral/CircleAverage.lean`. The companion work package C2, which builds on
these lemmas and is not part of this PR, stays in `VD/LLD/CircleAverageEstimates.lean`.
-/

open Complex ComplexConjugate

/--
Law of cosines for the chord from a point of the circle `circleMap 0 r` to an arbitrary point `a`.
See `norm_circleMap_zero_sub_sq'` for the half-angle form.
-/
theorem norm_circleMap_zero_sub_sq (r θ : ℝ) (a : ℂ) :
    ‖circleMap 0 r θ - a‖ ^ 2 = r ^ 2 + ‖a‖ ^ 2 - 2 * r * ‖a‖ * Real.cos (θ - a.arg) := by
  rw [← ofReal_inj, ← normSq_eq_norm_sq, normSq_sub]
  suffices (circleMap 0 r θ * conj a).re = r * ‖a‖ * Real.cos (θ - a.arg) by
    simp [normSq_eq_norm_sq, -mul_re, this, mul_assoc]
  conv_lhs => rw [← norm_mul_exp_arg_mul_I a, ← circleMap_zero, conj_circleMap_zero,
    circleMap_zero_mul, circleMap_zero_re, ← sub_eq_add_neg]

/--
Law of cosines for the chord from a point of the circle `circleMap 0 r` to an arbitrary point `a`,
half-angle form. For `r = 1` and `a = 1`, see also `Complex.norm_exp_I_mul_ofReal_sub_one`.
-/
theorem norm_circleMap_zero_sub_sq' (r θ : ℝ) (a : ℂ) :
    ‖circleMap 0 r θ - a‖ ^ 2
      = (r - ‖a‖) ^ 2 + 4 * r * ‖a‖ * Real.sin ((θ - a.arg) / 2) ^ 2 := by
  have h := Real.sin_sq_eq_half_sub ((θ - a.arg) / 2)
  rw [show 2 * ((θ - a.arg) / 2) = θ - a.arg by ring] at h
  rw [norm_circleMap_zero_sub_sq]
  linear_combination (-(4 * r * ‖a‖)) * h

/--
Points of the circle `circleMap 0 r` keep distance at least `r * |sin ((θ - arg a) / 2)|` from any
point `a`. The bound is sharp: equality holds for `a = 0` and `θ = π`.
-/
theorem mul_abs_sin_le_norm_circleMap_zero_sub {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) (a : ℂ) :
    r * |Real.sin ((θ - a.arg) / 2)| ≤ ‖circleMap 0 r θ - a‖ := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [mul_pow, sq_abs, norm_circleMap_zero_sub_sq']
  nlinarith [mul_nonneg (sub_nonneg.2 (Real.sin_sq_le_one ((θ - a.arg) / 2)))
      (sq_nonneg (r - ‖a‖)),
    mul_nonneg (mul_nonneg (sq_nonneg (Real.sin ((θ - a.arg) / 2))) (norm_nonneg a))
      (by positivity : (0 : ℝ) ≤ 2 * r + ‖a‖)]
