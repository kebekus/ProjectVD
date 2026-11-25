/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import VD.AlgebraicDependence.PointwiseEstimates

/-!
# A Bézout Estimate for `log⁺` of Quotients of Polynomial Expressions

Let `𝕜` be a normed division ring, let `w : 𝕜`, and let

- `P = w ^ p + ∑ j ∈ range p, a j * w ^ j` and
- `Q = w ^ q + ∑ k ∈ range q, b k * w ^ k`

be monic polynomial expressions in `w`. If numerator and denominator have no common zeros, one
expects that the quotient `P / Q` has the size of `w ^ (p - q)` where `w` is large, and that it is
large where `Q` is small. This file makes the expectation quantitative, under the assumption that
there is a Bézout identity `U * P + V * Q = 1`, where `U` and `V` are polynomial expressions in
`w` as well.

## Main results

- `Real.posLog_inv_norm_le_of_mul_add_mul_eq_one`: the scalar case. If `u * x + v * y = 1`, then
  `log⁺ ‖y‖⁻¹ ≤ log⁺ ‖x / y‖ + log⁺ ‖u‖ + log⁺ ‖v‖ + log 2`.
- `Real.mul_posLog_norm_add_posLog_inv_norm_le_of_mul_add_mul_eq_one`: the Bézout estimate for
  monic polynomial expressions. The number `p * log⁺ ‖w‖ + log⁺ ‖Q‖⁻¹` is at most
  `log⁺ ‖P / Q‖ + q * log⁺ ‖w‖`, plus an explicit error term that depends only on the degrees and
  on `log⁺` of the norms of the coefficients of `P`, `Q`, `U` and `V`.

## Implementation notes

As in the estimates for polynomial expressions that this file builds on, the results are stated
for sums over `Finset.range` and not for `Polynomial.eval`. For polynomials `P` and `Q` with
coefficients in a commutative ring, the existence of a Bézout identity is the definition of
`IsCoprime P Q`; evaluating the identity at `w` gives the assumption of the estimate.

The proof distinguishes two cases. If `w` is bounded in terms of the coefficients of `P` and `Q`,
then `log⁺ ‖w‖` is part of the error term, and the scalar case applies. Otherwise, `P` and `Q`
are comparable to their leading terms `w ^ p` and `w ^ q`.

## Motivation

In value distribution theory, the estimate is applied to the values of meromorphic functions and
averaged over circles. It yields the lower bound in the theorem of Valiron and Mohon'ko: if `f` is
meromorphic and `P`, `Q` are coprime polynomials whose coefficients grow slower than `f`, then
the Nevanlinna characteristic of `P(f) / Q(f)` is `max (deg P) (deg Q)` times that of `f`, up to
an error of smaller order.
-/

@[expose] public section

/-
# Upstreaming plan

Project context: this file is step G2 of work package G of the project's treatment of algebraic
dependence, see `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §9. It was split off from
`VD/AlgebraicDependence/PointwiseEstimates.lean` (work package A) on 2026-11-25, and builds on
that file. Its only consumer is `nsmul_characteristic_add_characteristic_inv_le_of_bezout` in
`VD/AlgebraicDependence/RationalCharacteristic.lean`, the lower bound in the theorem of Valiron
and Mohon'ko for rational functions.

Status: ready, as a second PR after the one that upstreams `PointwiseEstimates.lean`; see the
plan in that file. Apart from that PR, the material depends on Mathlib master only. It was
checked against the Mathlib revision pinned in `lake-manifest.json` (`d1166066`, 2026-11-25).

When to submit. Nothing here depends on `VD/Field/`, so the PR can be opened as soon as the
first one is merged. The consumer, however, needs the field of meromorphic functions, and item 7
of the PR list in §11 of the plan schedules it late. A special-purpose estimate with a statement
of this length is easier to review when its consumer is in sight. Recommendation: submit it
shortly before `RationalCharacteristic.lean`, and say in the PR description where it is used.

## Step 1: append to `Mathlib/Analysis/SpecialFunctions/Log/PosLogPolynomial.lean`

`PosLogPolynomial.lean` is the file that the first PR creates. Everything from the line
`section NormedDivisionRing` to the end of this file goes to the end of the target file,
unchanged. The section is needed there: the target file has the variables `R`, `a` and `w` in
scope, and the section keeps the new meaning of `w` local. The target file needs no new import. A
copy of the target file with this material appended compiles under Mathlib's linter set.

The module docstring of the target file gains
- a heading "Quotients of polynomial expressions." at the end of its section "Main results",
  followed by the two entries of the section "Main results" of this file,
- the second paragraph of the implementation notes of this file, and the last sentence of the
  first,
- the content of the section "Motivation" of this file, appended to its own.

The alternative is a new file `Mathlib/Analysis/SpecialFunctions/Log/PosLogBezout.lean` that
imports `PosLogPolynomial.lean`, with the module docstring of this file. It keeps the general
estimates apart from the special-purpose one, at the price of a file of some 100 lines. If
reviewers find the estimate too special for `Mathlib/Analysis/SpecialFunctions/`, it can move
into the file that proves the theorem of Valiron and Mohon'ko for rational functions; Mathlib's
`Mathlib/Analysis/Complex/ValueDistribution/SecondMainTheorem.lean` sets the precedent with the
separation lemma `Real.exists_sum_posLog_inv_norm_sub_le`.

## PR title and description (draft)

The paragraphs are wrapped to fit this file. Join the lines of each paragraph before pasting,
because GitHub renders line breaks in PR descriptions.

Title:

    feat(Analysis/SpecialFunctions/Log): a Bézout estimate for quotients of polynomial expressions

Description:

    Let `P` and `Q` be monic polynomial expressions of degrees `p` and `q` in a point `w` of a
    normed division ring, and assume that there is a Bézout identity `U * P + V * Q = 1`, where
    `U` and `V` are polynomial expressions in `w`. Establish the estimate

    `p * log⁺ ‖w‖ + log⁺ ‖Q‖⁻¹ ≤ log⁺ ‖P / Q‖ + q * log⁺ ‖w‖ + C`,

    where `C` is explicit and depends only on the degrees and on `log⁺` of the norms of the
    coefficients of `P`, `Q`, `U` and `V`. In other words: the quotient `P / Q` is as large as the
    degrees suggest, and it is large wherever the denominator is small.

    The proof rests on the scalar case `Real.posLog_inv_norm_le_of_mul_add_mul_eq_one`: if
    `u * x + v * y = 1`, then `log⁺ ‖y‖⁻¹ ≤ log⁺ ‖x / y‖ + log⁺ ‖u‖ + log⁺ ‖v‖ + log 2`.

    This material is typically used in complex analysis. The PR will be used in
    [Project VD](https://github.com/kebekus/ProjectVD), formalizing Value Distribution Theory for
    meromorphic functions on the complex plane, in order to establish the theorem of Valiron and
    Mohon'ko on the growth of rational functions in meromorphic functions. Claude Code was used
    to create this PR.

## Step 2: after the merge

- Delete this file and remove `VD.AlgebraicDependence.BezoutEstimate` from `VD.lean`.
- In `VD/AlgebraicDependence/RationalCharacteristic.lean`, replace the import of this file by
  `Mathlib.Analysis.SpecialFunctions.Log.PosLogPolynomial`.
- Update item 7 of the PR list in `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §11.

## Where the material ends up

| Declaration                                                         | Mathlib target            |
| ------------------------------------------------------------------- | ------------------------- |
| `Real.posLog_inv_norm_le_of_mul_add_mul_eq_one`                     | `PosLogPolynomial.lean`   |
| `Real.mul_posLog_norm_add_posLog_inv_norm_le_of_mul_add_mul_eq_one` | `PosLogPolynomial.lean`   |

Both declarations are public.
-/

open Finset Real

section NormedDivisionRing

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {w : 𝕜}

/-!
## The Bézout Estimate
-/

/-- **Bézout estimate, scalar case**: if `u * x + v * y = 1`, then
`log⁺ ‖y‖⁻¹ ≤ log⁺ ‖x / y‖ + log⁺ ‖u‖ + log⁺ ‖v‖ + log 2`. In other words, `y` is small only where
`x / y` is large, up to the size of the coefficients `u` and `v`. The constant `log 2` is the one
of `Real.posLog_norm_add_le`. -/
theorem Real.posLog_inv_norm_le_of_mul_add_mul_eq_one {x y u v : 𝕜} (h : u * x + v * y = 1) :
    log⁺ ‖y‖⁻¹ ≤ log⁺ ‖x / y‖ + log⁺ ‖u‖ + log⁺ ‖v‖ + log 2 := by
  obtain rfl | hy := eq_or_ne y 0
  · simpa using add_nonneg (add_nonneg posLog_nonneg posLog_nonneg) (log_nonneg one_le_two)
  -- Divide the Bézout identity by `y`, and apply the triangle inequality.
  have : y⁻¹ = u * (x / y) + v := by
    rw [div_eq_mul_inv, ← mul_assoc, ← mul_inv_cancel_right₀ hy v, ← add_mul, h, one_mul]
  rw [← norm_inv, this]
  grw [posLog_norm_add_le, norm_mul, posLog_mul]
  linarith

/-- **Bézout estimate for quotients of monic polynomial expressions**: let
`P = w ^ p + ∑ j ∈ range p, a j * w ^ j` and `Q = w ^ q + ∑ k ∈ range q, b k * w ^ k` be monic
polynomial expressions in `w`, and assume that the polynomial expressions
`U = ∑ i ∈ range (m + 1), u i * w ^ i` and `V = ∑ i ∈ range (n + 1), v i * w ^ i` satisfy the
Bézout identity `U * P + V * Q = 1`. Then `p * log⁺ ‖w‖ + log⁺ ‖Q‖⁻¹` is at most
`log⁺ ‖P / Q‖ + q * log⁺ ‖w‖ + (p + m + n + 3) * Λ`, where `Λ` is the sum of `log⁺` of the norms
of all coefficients of `P`, `Q`, `U` and `V`, plus
`log 2 + log p + log q + log (m + 1) + log (n + 1)`.

In other words, the quotient `P / Q` is as large as the degrees suggest, and it is large wherever
the denominator `Q` is small: up to the error term, `log⁺ ‖P / Q‖` is at least
`(p - q) * log⁺ ‖w‖ + log⁺ ‖Q‖⁻¹`. The estimate needs no assumption on `p` and `q`. The constants
are not optimized. -/
theorem Real.mul_posLog_norm_add_posLog_inv_norm_le_of_mul_add_mul_eq_one {p q m n : ℕ}
    {a b u v : ℕ → 𝕜}
    (h : (∑ i ∈ range (m + 1), u i * w ^ i) * (w ^ p + ∑ j ∈ range p, a j * w ^ j)
      + (∑ i ∈ range (n + 1), v i * w ^ i) * (w ^ q + ∑ k ∈ range q, b k * w ^ k) = 1) :
    p * log⁺ ‖w‖ + log⁺ ‖w ^ q + ∑ k ∈ range q, b k * w ^ k‖⁻¹
      ≤ log⁺ ‖(w ^ p + ∑ j ∈ range p, a j * w ^ j) / (w ^ q + ∑ k ∈ range q, b k * w ^ k)‖
        + q * log⁺ ‖w‖
        + (p + m + n + 3) * (∑ j ∈ range p, log⁺ ‖a j‖ + ∑ k ∈ range q, log⁺ ‖b k‖
          + ∑ i ∈ range (m + 1), log⁺ ‖u i‖ + ∑ i ∈ range (n + 1), log⁺ ‖v i‖
          + log 2 + log p + log q + log (m + 1) + log (n + 1)) := by
  set P := w ^ p + ∑ j ∈ range p, a j * w ^ j
  set Q := w ^ q + ∑ k ∈ range q, b k * w ^ k
  set Λ := ∑ j ∈ range p, log⁺ ‖a j‖ + ∑ k ∈ range q, log⁺ ‖b k‖
    + ∑ i ∈ range (m + 1), log⁺ ‖u i‖ + ∑ i ∈ range (n + 1), log⁺ ‖v i‖
    + log 2 + log p + log q + log (m + 1) + log (n + 1) with hΛ
  -- All summands of `Λ` are nonnegative.
  have hSa : 0 ≤ ∑ j ∈ range p, log⁺ ‖a j‖ := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hSb : 0 ≤ ∑ k ∈ range q, log⁺ ‖b k‖ := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hSu : 0 ≤ ∑ i ∈ range (m + 1), log⁺ ‖u i‖ := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hSv : 0 ≤ ∑ i ∈ range (n + 1), log⁺ ‖v i‖ := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hm : 0 ≤ log (m + 1 : ℝ) := log_nonneg (by simp)
  have hn : 0 ≤ log (n + 1 : ℝ) := log_nonneg (by simp)
  have hp : 0 ≤ log (p : ℝ) := log_natCast_nonneg p
  have hq : 0 ≤ log (q : ℝ) := log_natCast_nonneg q
  have h2 : 0 ≤ log (2 : ℝ) := log_nonneg one_le_two
  have hΛ₀ : 0 ≤ Λ := by positivity
  have hK : (0 : ℝ) ≤ p + m + n := by positivity
  have h2' : log⁺ (2 : ℝ) = log 2 := posLog_eq_log (by norm_num)
  by_cases! hw : ‖w‖ ≤ 1 ∨ ‖w‖ ≤ 2 * ∑ j ∈ range p, ‖a j‖ ∨ ‖w‖ ≤ 2 * ∑ k ∈ range q, ‖b k‖
  · -- If `w` is bounded in terms of the coefficients of `P` and `Q`, then `log⁺ ‖w‖ ≤ Λ`, and the
    -- scalar case applies.
    have hw' : log⁺ ‖w‖ ≤ Λ := by
      obtain hw | hw | hw := hw
      · rwa [(posLog_eq_zero_iff _).2 (by rwa [abs_norm])]
      all_goals
        grw [hw, posLog_mul, posLog_sum, card_range, h2']
        · linarith
        · exact neg_one_lt_zero.le.trans (norm_nonneg _)
    linarith [posLog_inv_norm_le_of_mul_add_mul_eq_one h, posLog_norm_sum_mul_pow_le m u w,
      posLog_norm_sum_mul_pow_le n v w, mul_nonneg hK (sub_nonneg.2 hw'),
      mul_nonneg q.cast_nonneg (posLog_nonneg (x := ‖w‖))]
  · -- Otherwise, `P` and `Q` are comparable to their leading terms `w ^ p` and `w ^ q`.
    obtain ⟨hw₁, hwA, hwB⟩ := hw
    have hP := norm_pow_le_two_mul_norm_pow_add_sum (a := a) (d := p) hw₁.le hwA.le
    have hQ := norm_pow_le_two_mul_norm_pow_add_sum (a := b) (d := q) hw₁.le hwB.le
    have hQ' := norm_pow_add_sum_le_two_mul_norm_pow (a := b) (d := q) hw₁.le hwB.le
    have hQ₁ : 1 ≤ 2 * ‖Q‖ := (one_le_pow₀ hw₁.le).trans hQ
    have hQ₀ : 0 < ‖Q‖ := by linarith
    have h₁ : log⁺ ‖Q‖⁻¹ ≤ log 2 := by
      grw [(inv_le_iff_one_le_mul₀ hQ₀).2 hQ₁, h2']
      exact neg_one_lt_zero.le.trans (by positivity)
    have h₂ : p * log⁺ ‖w‖ ≤ 2 * log 2 + log⁺ ‖P / Q‖ + q * log⁺ ‖w‖ := by
      have : ‖w‖ ^ p ≤ 2 * (‖P / Q‖ * (2 * ‖w‖ ^ q)) :=
        calc ‖w‖ ^ p
          _ ≤ 2 * ‖P‖ := hP
          _ = 2 * (‖P / Q‖ * ‖Q‖) := by rw [← norm_mul, div_mul_cancel₀ P (norm_pos_iff.1 hQ₀)]
          _ ≤ 2 * (‖P / Q‖ * (2 * ‖w‖ ^ q)) := by gcongr
      rw [← posLog_pow]
      grw [this, posLog_mul, posLog_mul, posLog_mul, posLog_pow, h2']
      · linarith
      · exact neg_one_lt_zero.le.trans (by positivity)
    linarith [mul_nonneg hK hΛ₀]

end NormedDivisionRing
