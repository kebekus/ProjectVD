/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Pointwise `log⁺` Estimates for Polynomial Relations — Algebraic Dependence work package A

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §3.

Mathlib target: `Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean` or a new sibling file.
Dependencies: none beyond `PosLog`. Pure `NormedField` algebra, no meromorphy, no integration.

This file collects the pointwise inequalities behind the algebraic dependence theorem, the
Valiron–Mohon'ko identity, Clunie's lemma and Mohon'ko's lemma of Nevanlinna theory. In each
case, a point `w` of a normed field satisfies a polynomial relation, and `log⁺ ‖w‖` (or `log⁺`
of a polynomial expression in `w`) is estimated in terms of `log⁺` of the coefficients.

## Main results

- `Real.nsmul_posLog_norm_le_of_monic_eq`: the **weighted root bound**
  `d · log⁺ ‖w‖ ≤ log⁺ ‖g‖ + d · Σ_{j<d} log⁺ ‖a j‖ + d · log (2 (d + 1))` for solutions of
  `w ^ d + Σ_{j<d} a j * w ^ j = g`. The factor `d` in front of `log⁺ ‖w‖` is what the Cauchy
  bound `Polynomial.IsRoot.norm_lt_cauchyBound` cannot give.
- `Real.posLog_norm_le_of_monic_eq_zero`: the unweighted bound with the sharper constant
  `log d`, for `g = 0`.
- `Real.posLog_norm_le_of_pow_mul_eq`: Clunie's lemma, pointwise.
- `Real.posLog_norm_inv_le_of_eq_zero`: Mohon'ko's lemma, pointwise (needs `a 0 ≠ 0`).
- `Real.posLog_norm_sum_mul_pow_le` (for package D): the upper bound
  `log⁺ ‖Σ_{j≤d} a j * w ^ j‖ ≤ d · log⁺ ‖w‖ + Σ_{j≤d} log⁺ ‖a j‖ + log (d + 1)`.
- `Real.nsmul_posLog_norm_add_posLog_norm_inv_le_of_bezout` (G2, for package G): Mohon'ko's
  **Bezout estimate** for a quotient of monic polynomial expressions with a Bezout certificate,
  the pointwise input for the lower bound of the rational Valiron–Mohon'ko identity.
-/

@[expose] public section

open Finset Real

namespace Real

variable {𝕜 : Type*} [NormedField 𝕜] {a : ℕ → 𝕜} {w : 𝕜}

/-!
## Elementary Norm Estimates for Polynomial Expressions
-/

/-- For `‖w‖ ≤ 1`, a polynomial expression in `w` is bounded by the sum of the norms of its
coefficients. -/
lemma norm_sum_mul_pow_le_of_norm_le_one {s : Finset ℕ} (hw : ‖w‖ ≤ 1) :
    ‖∑ j ∈ s, a j * w ^ j‖ ≤ ∑ j ∈ s, ‖a j‖ := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hw)

/-- For `1 ≤ ‖w‖`, a polynomial expression of degree less than `d` in `w` is bounded by
`‖w‖ ^ (d - 1)` times the sum of the norms of its coefficients. -/
lemma norm_sum_mul_pow_le_of_one_le_norm {d : ℕ} (hw : 1 ≤ ‖w‖) :
    ‖∑ j ∈ range (d + 1), a j * w ^ j‖ ≤ (∑ j ∈ range (d + 1), ‖a j‖) * ‖w‖ ^ d := by
  rw [sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j hj ↦ ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw (Nat.lt_succ_iff.1 (mem_range.1 hj)))
    (norm_nonneg _)

/--
**Upper bound for polynomial expressions.** `log⁺ ‖Σ_{j≤d} a j * w ^ j‖` is bounded by
`d · log⁺ ‖w‖ + Σ_{j≤d} log⁺ ‖a j‖ + log (d + 1)`. Note the factor `d` (and not
`Σ_{j≤d} j = d (d + 1) / 2`, which termwise estimation would give). -/
theorem posLog_norm_sum_mul_pow_le {d : ℕ} (a : ℕ → 𝕜) (w : 𝕜) :
    log⁺ ‖∑ j ∈ range (d + 1), a j * w ^ j‖
      ≤ d * log⁺ ‖w‖ + ∑ j ∈ range (d + 1), log⁺ ‖a j‖ + log (d + 1) := by
  have hS : log⁺ (∑ j ∈ range (d + 1), ‖a j‖)
      ≤ log (d + 1) + ∑ j ∈ range (d + 1), log⁺ ‖a j‖ := by
    simpa using posLog_sum (range (d + 1)) fun j ↦ ‖a j‖
  have hw0 : 0 ≤ d * log⁺ ‖w‖ := mul_nonneg (Nat.cast_nonneg d) posLog_nonneg
  rcases le_or_gt ‖w‖ 1 with hw | hw
  · calc log⁺ ‖∑ j ∈ range (d + 1), a j * w ^ j‖
        ≤ log⁺ (∑ j ∈ range (d + 1), ‖a j‖) :=
          posLog_le_posLog (by linarith [norm_nonneg (∑ j ∈ range (d + 1), a j * w ^ j)])
            (norm_sum_mul_pow_le_of_norm_le_one hw)
      _ ≤ _ := by linarith
  · calc log⁺ ‖∑ j ∈ range (d + 1), a j * w ^ j‖
        ≤ log⁺ ((∑ j ∈ range (d + 1), ‖a j‖) * ‖w‖ ^ d) :=
          posLog_le_posLog (by linarith [norm_nonneg (∑ j ∈ range (d + 1), a j * w ^ j)])
            (norm_sum_mul_pow_le_of_one_le_norm hw.le)
      _ ≤ log⁺ (∑ j ∈ range (d + 1), ‖a j‖) + log⁺ (‖w‖ ^ d) := posLog_mul
      _ = log⁺ (∑ j ∈ range (d + 1), ‖a j‖) + d * log⁺ ‖w‖ := by rw [posLog_pow]
      _ ≤ _ := by linarith

/-!
## Root Bounds
-/

/--
**Weighted root bound.** If `w` solves the monic equation `w ^ d + Σ_{j<d} a j * w ^ j = g`,
then `d · log⁺ ‖w‖ ≤ log⁺ ‖g‖ + d · Σ_{j<d} log⁺ ‖a j‖ + d · log (2 (d + 1))`.

The factor `d` in front of `log⁺ ‖w‖` — as opposed to the Cauchy bound
`Polynomial.IsRoot.norm_lt_cauchyBound`, which only gives `log⁺ ‖w‖ ≤ log⁺ ‖g‖ + …` — is
the whole point: it is the source of the factor `deg P` in the Valiron–Mohon'ko identity.
-/
theorem nsmul_posLog_norm_le_of_monic_eq {d : ℕ} {g : 𝕜}
    (h : w ^ d + ∑ j ∈ range d, a j * w ^ j = g) :
    d * log⁺ ‖w‖ ≤ log⁺ ‖g‖ + d * ∑ j ∈ range d, log⁺ ‖a j‖ + d * log (2 * (d + 1)) := by
  rcases d with _ | d
  · simp [posLog_nonneg]
  push_cast
  set S := ∑ j ∈ range (d + 1), ‖a j‖ with hS
  have hS₀ : 0 ≤ S := sum_nonneg fun _ _ ↦ norm_nonneg _
  have hsum₀ : 0 ≤ ∑ j ∈ range (d + 1), log⁺ ‖a j‖ := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hd : (0 : ℝ) ≤ d + 1 := by positivity
  have hg₀ : 0 ≤ log⁺ ‖g‖ := posLog_nonneg
  -- The constant: `log (1 + S) ≤ log (d + 2) + Σ log⁺ ‖a j‖`, via the largest coefficient.
  have hlog : log (1 + S) ≤ log (d + 1 + 1) + ∑ j ∈ range (d + 1), log⁺ ‖a j‖ := by
    obtain ⟨m, hm, hmax⟩ := (range (d + 1)).exists_max_image (fun j ↦ ‖a j‖)
      ⟨0, mem_range.2 (Nat.succ_pos d)⟩
    have h₁ : 1 + S ≤ (d + 1 + 1) * max 1 ‖a m‖ := by
      have : S ≤ (d + 1) * max 1 ‖a m‖ := by
        calc S ≤ ∑ j ∈ range (d + 1), max 1 ‖a m‖ :=
              sum_le_sum fun j hj ↦ (hmax j hj).trans (le_max_right _ _)
          _ = (d + 1) * max 1 ‖a m‖ := by simp
      linarith [le_max_left 1 ‖a m‖]
    calc log (1 + S) ≤ log ((d + 1 + 1) * max 1 ‖a m‖) := log_le_log (by positivity) h₁
      _ = log (d + 1 + 1) + log (max 1 ‖a m‖) := log_mul (by positivity) (by positivity)
      _ = log (d + 1 + 1) + log⁺ ‖a m‖ := by rw [posLog_eq_log_max_one (norm_nonneg _)]
      _ ≤ _ := by
          gcongr
          exact single_le_sum (f := fun j ↦ log⁺ ‖a j‖) (fun _ _ ↦ posLog_nonneg) hm
  have hlog2 : log 2 ≤ (d + 1) * log (2 * (d + 1 + 1)) := by
    have h₁ : log 2 ≤ log (2 * (d + 1 + 1)) := log_le_log two_pos (by linarith)
    have h₂ : 0 ≤ log (2 * (d + 1 + 1)) := log_nonneg (by linarith)
    nlinarith
  rcases lt_or_ge ‖w‖ (2 * (1 + S)) with hw | hw
  · -- Case `‖w‖ < 2 (1 + S)`: the left-hand side is bounded by the constant.
    have h₁ : log⁺ ‖w‖ ≤ log 2 + log (1 + S) := by
      calc log⁺ ‖w‖ ≤ log⁺ (2 * (1 + S)) := posLog_le_posLog (by linarith [norm_nonneg w]) hw.le
        _ = log (2 * (1 + S)) := posLog_eq_log (by rw [abs_of_pos (by positivity)]; linarith)
        _ = log 2 + log (1 + S) := log_mul two_ne_zero (by positivity)
    rw [log_mul two_ne_zero (by positivity)]
    calc (d + 1) * log⁺ ‖w‖
        ≤ (d + 1) * (log 2 + (log (d + 1 + 1) + ∑ j ∈ range (d + 1), log⁺ ‖a j‖)) := by
          gcongr
          exact h₁.trans (by linarith)
      _ ≤ _ := by nlinarith
  · -- Case `2 (1 + S) ≤ ‖w‖`: the leading term dominates, `‖w‖ ^ (d + 1) ≤ 2 ‖g‖`.
    have hw1 : 1 ≤ ‖w‖ := by linarith
    have hpow : ‖w‖ ^ (d + 1) ≤ 2 * ‖g‖ := by
      have h₁ : ‖w‖ ^ (d + 1) ≤ ‖g‖ + S * ‖w‖ ^ d := by
        calc ‖w‖ ^ (d + 1) = ‖w ^ (d + 1)‖ := (norm_pow _ _).symm
          _ = ‖g - ∑ j ∈ range (d + 1), a j * w ^ j‖ := by rw [eq_sub_of_add_eq h]
          _ ≤ ‖g‖ + ‖∑ j ∈ range (d + 1), a j * w ^ j‖ := norm_sub_le _ _
          _ ≤ ‖g‖ + S * ‖w‖ ^ d := by gcongr; exact norm_sum_mul_pow_le_of_one_le_norm hw1
      have h₂ : S * ‖w‖ ^ d ≤ ‖w‖ ^ (d + 1) / 2 := by
        rw [pow_succ]
        calc S * ‖w‖ ^ d ≤ (‖w‖ / 2) * ‖w‖ ^ d := by gcongr; linarith
          _ = ‖w‖ ^ d * ‖w‖ / 2 := by ring
      linarith
    have hg : 0 < ‖g‖ := by
      have : 0 < ‖w‖ ^ (d + 1) := by positivity
      linarith
    have hlogg : log ‖g‖ ≤ log⁺ ‖g‖ := le_max_right _ _
    rw [posLog_eq_log (by rwa [abs_norm])]
    calc (d + 1 : ℝ) * log ‖w‖ = log (‖w‖ ^ (d + 1)) := by rw [log_pow]; push_cast; ring
      _ ≤ log (2 * ‖g‖) := log_le_log (by positivity) hpow
      _ = log 2 + log ‖g‖ := log_mul two_ne_zero hg.ne'
      _ ≤ _ := by nlinarith

/--
**Unweighted root bound.** If `w` solves the monic equation `w ^ d + Σ_{j<d} a j * w ^ j = 0`,
then `log⁺ ‖w‖ ≤ Σ_{j<d} log⁺ ‖a j‖ + log d`. Compare `Real.nsmul_posLog_norm_le_of_monic_eq`,
which has a worse constant but a factor `d` on the left.
-/
theorem posLog_norm_le_of_monic_eq_zero {d : ℕ}
    (h : w ^ d + ∑ j ∈ range d, a j * w ^ j = 0) :
    log⁺ ‖w‖ ≤ ∑ j ∈ range d, log⁺ ‖a j‖ + log d := by
  rcases d with _ | d
  · simp at h
  push_cast
  have hsum₀ : 0 ≤ ∑ j ∈ range (d + 1), log⁺ ‖a j‖ := sum_nonneg fun _ _ ↦ posLog_nonneg
  rcases le_or_gt ‖w‖ 1 with hw | hw
  · rw [(posLog_eq_zero_iff _).2 (by rwa [abs_norm])]
    have : 0 ≤ log (d + 1) := log_nonneg (by linarith)
    linarith
  · -- `‖w‖ > 1`: from `‖w‖ ^ (d + 1) ≤ (Σ ‖a j‖) ‖w‖ ^ d` we get `‖w‖ ≤ Σ ‖a j‖`.
    have key : ‖w‖ ≤ ∑ j ∈ range (d + 1), ‖a j‖ := by
      have h₁ : ‖w‖ ^ (d + 1) ≤ (∑ j ∈ range (d + 1), ‖a j‖) * ‖w‖ ^ d := by
        rw [← norm_pow, eq_neg_of_add_eq_zero_left h, norm_neg]
        exact norm_sum_mul_pow_le_of_one_le_norm hw.le
      have hpos : 0 < ‖w‖ ^ d := by positivity
      rw [pow_succ, mul_comm] at h₁
      exact le_of_mul_le_mul_right h₁ hpos
    calc log⁺ ‖w‖ ≤ log⁺ (∑ j ∈ range (d + 1), ‖a j‖) :=
          posLog_le_posLog (by linarith [norm_nonneg w]) key
      _ ≤ log #(range (d + 1)) + ∑ j ∈ range (d + 1), log⁺ ‖a j‖ := posLog_sum _ _
      _ = _ := by simp [add_comm]

/-!
## Clunie's Lemma and Mohon'ko's Lemma, Pointwise
-/

/--
**Clunie's lemma, pointwise.** If `w ^ n * P(w) = Q(w)` for polynomial expressions `P` and `Q`
with `deg Q ≤ n`, then `log⁺ ‖P(w)‖` is bounded by the sum of `log⁺` of all coefficients of `P`
and `Q`, plus a constant.
-/
theorem posLog_norm_le_of_pow_mul_eq {n p : ℕ} {b : ℕ → 𝕜}
    (h : w ^ n * (∑ j ∈ range (p + 1), a j * w ^ j) = ∑ k ∈ range (n + 1), b k * w ^ k) :
    log⁺ ‖∑ j ∈ range (p + 1), a j * w ^ j‖
      ≤ ∑ j ∈ range (p + 1), log⁺ ‖a j‖ + ∑ k ∈ range (n + 1), log⁺ ‖b k‖
        + log (max (p + 1) (n + 1)) := by
  have hA : 0 ≤ ∑ j ∈ range (p + 1), log⁺ ‖a j‖ := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hB : 0 ≤ ∑ k ∈ range (n + 1), log⁺ ‖b k‖ := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hmax₁ : log (p + 1) ≤ log (max (p + 1) (n + 1)) :=
    log_le_log (by positivity) (le_max_left _ _)
  have hmax₂ : log (n + 1) ≤ log (max (p + 1) (n + 1)) :=
    log_le_log (by positivity) (le_max_right _ _)
  rcases le_or_gt ‖w‖ 1 with hw | hw
  · -- `‖w‖ ≤ 1`: `P(w)` is bounded by the coefficients of `P`.
    calc log⁺ ‖∑ j ∈ range (p + 1), a j * w ^ j‖
        ≤ log⁺ (∑ j ∈ range (p + 1), ‖a j‖) :=
          posLog_le_posLog (by linarith [norm_nonneg (∑ j ∈ range (p + 1), a j * w ^ j)])
            (norm_sum_mul_pow_le_of_norm_le_one hw)
      _ ≤ log #(range (p + 1)) + ∑ j ∈ range (p + 1), log⁺ ‖a j‖ := posLog_sum _ _
      _ ≤ _ := by simp only [card_range]; push_cast; linarith
  · -- `‖w‖ > 1`: `P(w) = Q(w) / w ^ n` is bounded by the coefficients of `Q`.
    have hP : ‖∑ j ∈ range (p + 1), a j * w ^ j‖ ≤ ∑ k ∈ range (n + 1), ‖b k‖ := by
      have hwn : 0 < ‖w‖ ^ n := by positivity
      have h₁ : ‖w‖ ^ n * ‖∑ j ∈ range (p + 1), a j * w ^ j‖
          ≤ (∑ k ∈ range (n + 1), ‖b k‖) * ‖w‖ ^ n := by
        calc ‖w‖ ^ n * ‖∑ j ∈ range (p + 1), a j * w ^ j‖
            = ‖∑ k ∈ range (n + 1), b k * w ^ k‖ := by rw [← norm_pow, ← norm_mul, h]
          _ ≤ _ := norm_sum_mul_pow_le_of_one_le_norm hw.le
      rw [mul_comm] at h₁
      exact le_of_mul_le_mul_right h₁ hwn
    calc log⁺ ‖∑ j ∈ range (p + 1), a j * w ^ j‖
        ≤ log⁺ (∑ k ∈ range (n + 1), ‖b k‖) :=
          posLog_le_posLog (by linarith [norm_nonneg (∑ j ∈ range (p + 1), a j * w ^ j)]) hP
      _ ≤ log #(range (n + 1)) + ∑ k ∈ range (n + 1), log⁺ ‖b k‖ := posLog_sum _ _
      _ ≤ _ := by simp only [card_range]; push_cast; linarith

/--
**Mohon'ko's lemma, pointwise.** If `w` solves `Σ_{j≤d} a j * w ^ j = 0` with constant
coefficient `a 0 ≠ 0`, then `log⁺ ‖w‖⁻¹ ≤ log⁺ ‖a 0‖⁻¹ + Σ_{1≤j≤d} log⁺ ‖a j‖ + log d`.

The hypothesis `a 0 ≠ 0` cannot be dropped: at points where `a 0` vanishes, the right-hand side
degenerates to `log⁺ 0⁻¹ = 0` and the inequality fails for small `w`.
-/
theorem posLog_norm_inv_le_of_eq_zero {d : ℕ}
    (h : ∑ j ∈ range (d + 1), a j * w ^ j = 0) (h₀ : a 0 ≠ 0) :
    log⁺ ‖w‖⁻¹ ≤ log⁺ ‖a 0‖⁻¹ + ∑ j ∈ Ico 1 (d + 1), log⁺ ‖a j‖ + log d := by
  rcases d with _ | d
  · rw [zero_add, sum_range_one, pow_zero, mul_one] at h
    exact absurd h h₀
  push_cast
  -- Re-index the sum over `Ico 1 (d + 2)` as a sum over `range (d + 1)`.
  have hIco : ∑ j ∈ Ico 1 (d + 1 + 1), log⁺ ‖a j‖ = ∑ i ∈ range (d + 1), log⁺ ‖a (i + 1)‖ := by
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact sum_congr rfl fun i _ ↦ by rw [add_comm]
  rw [hIco]
  have hsum₀ : 0 ≤ ∑ i ∈ range (d + 1), log⁺ ‖a (i + 1)‖ := sum_nonneg fun _ _ ↦ posLog_nonneg
  have ha₀ : 0 ≤ log⁺ ‖a 0‖⁻¹ := posLog_nonneg
  rcases le_or_gt 1 ‖w‖ with hw | hw
  · -- `1 ≤ ‖w‖`: the left-hand side vanishes.
    have h₁ : |‖w‖⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ hw
    rw [(posLog_eq_zero_iff _).2 h₁]
    have : 0 ≤ log (d + 1) := log_nonneg (by linarith)
    linarith
  · -- `‖w‖ < 1`: isolate `a 0 = -w · Σ_{i≤d} a (i + 1) * w ^ i` and estimate.
    have hw0 : w ≠ 0 := by
      rintro rfl
      apply h₀
      simpa [sum_range_succ', pow_succ] using h
    have hkey : ‖a 0‖ ≤ ‖w‖ * ∑ i ∈ range (d + 1), ‖a (i + 1)‖ := by
      have h₁ : ∑ i ∈ range (d + 1), a (i + 1) * w ^ (i + 1)
          = w * ∑ i ∈ range (d + 1), a (i + 1) * w ^ i := by
        rw [mul_sum]
        exact sum_congr rfl fun i _ ↦ by ring
      rw [sum_range_succ', h₁, pow_zero, mul_one] at h
      rw [eq_neg_of_add_eq_zero_right h, norm_neg, norm_mul]
      gcongr
      exact norm_sum_mul_pow_le_of_norm_le_one hw.le
    have hT : ‖w‖⁻¹ ≤ ‖a 0‖⁻¹ * ∑ i ∈ range (d + 1), ‖a (i + 1)‖ := by
      have ha0 : 0 < ‖a 0‖ := norm_pos_iff.2 h₀
      have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
      rw [← div_eq_inv_mul, le_div_iff₀ ha0, inv_mul_le_iff₀ hwpos]
      exact hkey
    calc log⁺ ‖w‖⁻¹ ≤ log⁺ (‖a 0‖⁻¹ * ∑ i ∈ range (d + 1), ‖a (i + 1)‖) :=
          posLog_le_posLog (by linarith [inv_nonneg.2 (norm_nonneg w)]) hT
      _ ≤ log⁺ ‖a 0‖⁻¹ + log⁺ (∑ i ∈ range (d + 1), ‖a (i + 1)‖) := posLog_mul
      _ ≤ log⁺ ‖a 0‖⁻¹ + (log #(range (d + 1)) + ∑ i ∈ range (d + 1), log⁺ ‖a (i + 1)‖) := by
          gcongr; exact posLog_sum _ _
      _ = _ := by simp only [card_range]; push_cast; ring

/-!
## The Bezout Estimate

The pointwise input for the lower bound of the rational Valiron–Mohon'ko identity (plan §9,
G2). If `P` and `Q` are monic polynomial expressions of degrees `p ≥ q` with a Bezout
certificate `U * P + V * Q = 1`, then `(p - q) · log⁺ ‖w‖ + log⁺ ‖Q(w)‖⁻¹` is bounded by
`log⁺ ‖P(w) / Q(w)‖` up to `log⁺` of the coefficients of `P`, `Q`, `U`, `V`. For large `‖w‖`
the leading terms dominate; for bounded `‖w‖` the Bezout identity shows that `Q(w)` can only be
small where `P(w)` is not.
-/

/-- **Bezout estimate, scalar form.** If `u * x + v * y = 1`, then
`log⁺ ‖y‖⁻¹ ≤ log⁺ ‖x / y‖ + log⁺ ‖u‖ + log⁺ ‖v‖ + log 2`: `y` can only be small where `x / y`
is large, up to the size of the Bezout coefficients. -/
theorem posLog_norm_inv_le_of_bezout {x y u v : 𝕜} (h : u * x + v * y = 1) :
    log⁺ ‖y‖⁻¹ ≤ log⁺ ‖x / y‖ + log⁺ ‖u‖ + log⁺ ‖v‖ + log 2 := by
  have hu : 0 ≤ log⁺ ‖u‖ := posLog_nonneg
  have hv : 0 ≤ log⁺ ‖v‖ := posLog_nonneg
  have hxy : 0 ≤ log⁺ ‖x / y‖ := posLog_nonneg
  have h2 : 0 ≤ log 2 := log_nonneg one_le_two
  have hlog2 : log⁺ (2 : ℝ) = log 2 := posLog_eq_log (by norm_num)
  rcases le_or_gt 1 ‖y‖ with hy | hy
  · -- `1 ≤ ‖y‖`: the left-hand side vanishes.
    rw [(posLog_eq_zero_iff _).2
      (by rw [abs_of_nonneg (inv_nonneg.2 (norm_nonneg _))]; exact inv_le_one_of_one_le₀ hy)]
    linarith
  rcases eq_or_ne y 0 with rfl | hy0
  · simp only [norm_zero, inv_zero, posLog_zero]
    linarith
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
  rcases le_or_gt (1 / 2) ‖v * y‖ with hvy | hvy
  · -- `‖v y‖ ≥ 1/2`: then `‖y‖⁻¹ ≤ 2 ‖v‖`.
    have h₁ : ‖y‖⁻¹ ≤ 2 * ‖v‖ := by
      rw [norm_mul] at hvy
      rw [inv_le_iff_one_le_mul₀ hypos]
      linarith
    calc log⁺ ‖y‖⁻¹ ≤ log⁺ (2 * ‖v‖) :=
          posLog_le_posLog (by linarith [inv_nonneg.2 (norm_nonneg y)]) h₁
      _ ≤ log⁺ 2 + log⁺ ‖v‖ := posLog_mul
      _ ≤ _ := by rw [hlog2]; linarith
  · -- `‖v y‖ < 1/2`: then `‖u x‖ ≥ 1/2` and `‖y‖⁻¹ ≤ 2 ‖u‖ ‖x / y‖`.
    have hux : 1 / 2 ≤ ‖u * x‖ := by
      rw [eq_sub_of_add_eq h]
      have := norm_sub_norm_le (1 : 𝕜) (v * y)
      rw [norm_one] at this
      linarith
    have h₁ : ‖y‖⁻¹ ≤ 2 * ‖u‖ * ‖x / y‖ := by
      rw [norm_mul] at hux
      rw [norm_div, ← mul_div_assoc, le_div_iff₀ hypos, inv_mul_cancel₀ hypos.ne']
      linarith
    calc log⁺ ‖y‖⁻¹ ≤ log⁺ (2 * ‖u‖ * ‖x / y‖) :=
          posLog_le_posLog (by linarith [inv_nonneg.2 (norm_nonneg y)]) h₁
      _ ≤ log⁺ (2 * ‖u‖) + log⁺ ‖x / y‖ := posLog_mul
      _ ≤ log⁺ 2 + log⁺ ‖u‖ + log⁺ ‖x / y‖ := by linarith [posLog_mul (x := 2) (y := ‖u‖)]
      _ ≤ _ := by rw [hlog2]; linarith

/-- For `1 ≤ ‖w‖`, a polynomial expression in `w` with exponents at most `d` is bounded by
`‖w‖ ^ d` times the sum of the norms of its coefficients. -/
lemma norm_sum_mul_pow_le_of_one_le_norm' {s : Finset ℕ} {d : ℕ} (hw : 1 ≤ ‖w‖)
    (hs : ∀ j ∈ s, j ≤ d) :
    ‖∑ j ∈ s, a j * w ^ j‖ ≤ (∑ j ∈ s, ‖a j‖) * ‖w‖ ^ d := by
  rw [sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j hj ↦ ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw (hs j hj)) (norm_nonneg _)

/-- For `‖w‖ ≥ max 1 (2 Σ_{j<d} ‖a j‖)`, the leading term of a monic polynomial expression
dominates: `‖w‖ ^ d ≤ 2 ‖w ^ d + Σ_{j<d} a j * w ^ j‖`. -/
lemma pow_le_two_mul_norm_monic {d : ℕ} (hw₁ : 1 ≤ ‖w‖)
    (hw₂ : 2 * ∑ j ∈ range d, ‖a j‖ ≤ ‖w‖) :
    ‖w‖ ^ d ≤ 2 * ‖w ^ d + ∑ j ∈ range d, a j * w ^ j‖ := by
  rcases d with _ | d
  · simp
  have h₁ : ‖∑ j ∈ range (d + 1), a j * w ^ j‖ ≤ (∑ j ∈ range (d + 1), ‖a j‖) * ‖w‖ ^ d :=
    norm_sum_mul_pow_le_of_one_le_norm hw₁
  have h₂ : (∑ j ∈ range (d + 1), ‖a j‖) * ‖w‖ ^ d ≤ ‖w‖ ^ (d + 1) / 2 := by
    rw [pow_succ]
    nlinarith [pow_nonneg (norm_nonneg w) d]
  have h₃ := norm_le_norm_add_norm_sub' (w ^ (d + 1))
    (w ^ (d + 1) + ∑ j ∈ range (d + 1), a j * w ^ j)
  rw [sub_add_cancel_left, norm_neg, norm_pow] at h₃
  linarith

/--
**Bezout estimate for monic polynomial expressions** (G2). Let `P(w) = w ^ p + Σ_{j<p} a j * w ^ j`
and `Q(w) = w ^ q + Σ_{k<q} b k * w ^ k` be monic polynomial expressions of degrees `q ≤ p`, and let
`U(w) = Σ_{i≤m} u i * w ^ i`, `V(w) = Σ_{i≤n} v i * w ^ i` satisfy the Bezout identity
`U(w) P(w) + V(w) Q(w) = 1`. Then
`(p - q) · log⁺ ‖w‖ + log⁺ ‖Q(w)‖⁻¹ ≤ log⁺ ‖P(w) / Q(w)‖ + (p + m + n + 3) · Λ`, where `Λ` is the
sum of `log⁺` of all coefficients of `P`, `Q`, `U`, `V` plus `log 2 + log p + log q + log (m + 1)
+ log (n + 1)`.

This is Mohon'ko's pointwise estimate: integrated over a circle and combined with the
corresponding divisor estimate, it gives the lower bound `max p q · T(r, f) ≤ T(r, P(f)/Q(f)) + S`
of the rational Valiron–Mohon'ko identity. The constants are not optimized.
-/
theorem nsmul_posLog_norm_add_posLog_norm_inv_le_of_bezout {p q m n : ℕ} (hqp : q ≤ p)
    {b u v : ℕ → 𝕜}
    (h : (∑ i ∈ range (m + 1), u i * w ^ i) * (w ^ p + ∑ j ∈ range p, a j * w ^ j)
      + (∑ i ∈ range (n + 1), v i * w ^ i) * (w ^ q + ∑ k ∈ range q, b k * w ^ k) = 1) :
    ((p - q : ℕ) : ℝ) * log⁺ ‖w‖ + log⁺ ‖w ^ q + ∑ k ∈ range q, b k * w ^ k‖⁻¹
      ≤ log⁺ ‖(w ^ p + ∑ j ∈ range p, a j * w ^ j) / (w ^ q + ∑ k ∈ range q, b k * w ^ k)‖
        + (p + m + n + 3) * (∑ j ∈ range p, log⁺ ‖a j‖ + ∑ k ∈ range q, log⁺ ‖b k‖
          + ∑ i ∈ range (m + 1), log⁺ ‖u i‖ + ∑ i ∈ range (n + 1), log⁺ ‖v i‖
          + log 2 + log p + log q + log (m + 1) + log (n + 1)) := by
  set Pw := w ^ p + ∑ j ∈ range p, a j * w ^ j with hPw
  set Qw := w ^ q + ∑ k ∈ range q, b k * w ^ k with hQw
  set Uw := ∑ i ∈ range (m + 1), u i * w ^ i with hUw
  set Vw := ∑ i ∈ range (n + 1), v i * w ^ i with hVw
  set A := ∑ j ∈ range p, ‖a j‖ with hA
  set B := ∑ k ∈ range q, ‖b k‖ with hB
  set Sa := ∑ j ∈ range p, log⁺ ‖a j‖ with hSa
  set Sb := ∑ k ∈ range q, log⁺ ‖b k‖ with hSb
  set Su := ∑ i ∈ range (m + 1), log⁺ ‖u i‖ with hSu
  set Sv := ∑ i ∈ range (n + 1), log⁺ ‖v i‖ with hSv
  set Λ := Sa + Sb + Su + Sv + log 2 + log p + log q + log (m + 1) + log (n + 1) with hΛ
  -- Nonnegativity of everything in sight.
  have hA₀ : 0 ≤ A := sum_nonneg fun _ _ ↦ norm_nonneg _
  have hB₀ : 0 ≤ B := sum_nonneg fun _ _ ↦ norm_nonneg _
  have hSa₀ : 0 ≤ Sa := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hSb₀ : 0 ≤ Sb := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hSu₀ : 0 ≤ Su := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hSv₀ : 0 ≤ Sv := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hlog2 : 0 ≤ log 2 := log_nonneg one_le_two
  have hlogp : 0 ≤ log (p : ℝ) := log_natCast_nonneg p
  have hlogq : 0 ≤ log (q : ℝ) := log_natCast_nonneg q
  have hlogm : 0 ≤ log ((m : ℝ) + 1) := log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hlogn : 0 ≤ log ((n : ℝ) + 1) := log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hΛ₀ : 0 ≤ Λ := by positivity
  have hK₀ : (0 : ℝ) ≤ p + m + n := by positivity
  have hpq : ((p - q : ℕ) : ℝ) = p - q := Nat.cast_sub hqp
  have hpq₀ : (0 : ℝ) ≤ p - q := by rw [← hpq]; positivity
  have hg₀ : 0 ≤ log⁺ ‖Pw / Qw‖ := posLog_nonneg
  -- `log⁺` of the coefficient sums.
  have hlogA : log⁺ A ≤ log p + Sa := by simpa using posLog_sum (range p) fun j ↦ ‖a j‖
  have hlogB : log⁺ B ≤ log q + Sb := by simpa using posLog_sum (range q) fun k ↦ ‖b k‖
  -- The radius separating the two regions.
  set R := max 1 (max (2 * A) (2 * B)) with hR
  have hR1 : 1 ≤ R := le_max_left _ _
  have hlogR : log R ≤ Λ := by
    have h₁ : R ≤ 2 * max 1 (max A B) := by
      simp only [hR, max_le_iff]
      refine ⟨by linarith [le_max_left 1 (max A B)], ?_, ?_⟩
      · linarith [le_max_left A B, le_max_right 1 (max A B)]
      · linarith [le_max_right A B, le_max_right 1 (max A B)]
    have h₂ : log⁺ (max A B) ≤ log⁺ A + log⁺ B := by
      rcases le_total A B with h | h
      · rw [max_eq_right h]; linarith [posLog_nonneg (x := A)]
      · rw [max_eq_left h]; linarith [posLog_nonneg (x := B)]
    calc log R ≤ log (2 * max 1 (max A B)) := log_le_log (by positivity) h₁
      _ = log 2 + log (max 1 (max A B)) := log_mul two_ne_zero (by positivity)
      _ = log 2 + log⁺ (max A B) := by rw [posLog_eq_log_max_one (le_max_of_le_left hA₀)]
      _ ≤ _ := by linarith
  rcases le_or_gt R ‖w‖ with hw | hw
  · -- Region `‖w‖ ≥ R`: the leading terms dominate.
    have hw1 : 1 ≤ ‖w‖ := hR1.trans hw
    have hwA : 2 * A ≤ ‖w‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
    have hwB : 2 * B ≤ ‖w‖ := ((le_max_right _ _).trans (le_max_right _ _)).trans hw
    have hP := pow_le_two_mul_norm_monic (a := a) (d := p) hw1 hwA
    have hQ := pow_le_two_mul_norm_monic (a := b) (d := q) hw1 hwB
    have hwp : 1 ≤ ‖w‖ ^ p := one_le_pow₀ hw1
    have hwq : 1 ≤ ‖w‖ ^ q := one_le_pow₀ hw1
    have hPpos : 0 < ‖Pw‖ := by linarith
    have hQpos : 0 < ‖Qw‖ := by linarith
    have hQup : ‖Qw‖ ≤ (1 + B) * ‖w‖ ^ q := by
      calc ‖Qw‖ ≤ ‖w ^ q‖ + ‖∑ k ∈ range q, b k * w ^ k‖ := norm_add_le _ _
        _ ≤ ‖w‖ ^ q + B * ‖w‖ ^ q := by
            rw [norm_pow]
            gcongr
            exact norm_sum_mul_pow_le_of_one_le_norm' hw1 fun k hk ↦ (mem_range.1 hk).le
        _ = _ := by ring
    -- `log⁺ ‖Qw‖⁻¹ ≤ log 2`.
    have h₁ : log⁺ ‖Qw‖⁻¹ ≤ log 2 := by
      have : ‖Qw‖⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hQpos two_pos]
        linarith
      calc log⁺ ‖Qw‖⁻¹ ≤ log⁺ 2 :=
            posLog_le_posLog (by linarith [inv_nonneg.2 (norm_nonneg Qw)]) this
        _ = log 2 := posLog_eq_log (by norm_num)
    -- `(p - q) log ‖w‖ ≤ log⁺ ‖Pw / Qw‖ + 2 log 2 + log⁺ B`.
    have h₂ : ((p : ℝ) - q) * log ‖w‖ ≤ log⁺ ‖Pw / Qw‖ + 2 * log 2 + log⁺ B := by
      have hdiv : ‖w‖ ^ p / (2 * ((1 + B) * ‖w‖ ^ q)) ≤ ‖Pw / Qw‖ := by
        rw [norm_div]
        calc ‖w‖ ^ p / (2 * ((1 + B) * ‖w‖ ^ q)) ≤ 2 * ‖Pw‖ / (2 * ‖Qw‖) :=
              div_le_div₀ (by positivity) hP (by positivity) (by linarith)
          _ = ‖Pw‖ / ‖Qw‖ := mul_div_mul_left _ _ two_ne_zero
      have hlog := log_le_log (by positivity) hdiv
      rw [log_div (by positivity) (by positivity), log_pow, log_mul two_ne_zero (by positivity),
        log_mul (by positivity) (by positivity), log_pow] at hlog
      have h₁ := log_one_add_le_posLog (x := B)
      have h₂ : log ‖Pw / Qw‖ ≤ log⁺ ‖Pw / Qw‖ := le_max_right _ _
      linarith
    rw [posLog_eq_log (by rwa [abs_norm]), hpq]
    have h₃ : 3 * Λ ≤ (p + m + n + 3) * Λ := by nlinarith
    linarith
  · -- Region `‖w‖ < R`: `log⁺ ‖w‖` is bounded, and the Bezout identity controls `Qw`.
    have hlogw : log⁺ ‖w‖ ≤ Λ := by
      calc log⁺ ‖w‖ ≤ log⁺ R := posLog_le_posLog (by linarith [norm_nonneg w]) hw.le
        _ = log R := posLog_eq_log (by rw [abs_of_pos (by linarith)]; exact hR1)
        _ ≤ Λ := hlogR
    have hbez := posLog_norm_inv_le_of_bezout h
    have hU : log⁺ ‖Uw‖ ≤ m * log⁺ ‖w‖ + Su + log (m + 1) := posLog_norm_sum_mul_pow_le u w
    have hV : log⁺ ‖Vw‖ ≤ n * log⁺ ‖w‖ + Sv + log (n + 1) := posLog_norm_sum_mul_pow_le v w
    have hlogw₀ : 0 ≤ log⁺ ‖w‖ := posLog_nonneg
    have h₁ : ((p : ℝ) - q) * log⁺ ‖w‖ ≤ ((p : ℝ) - q) * Λ :=
      mul_le_mul_of_nonneg_left hlogw hpq₀
    have h₂ : (m : ℝ) * log⁺ ‖w‖ ≤ m * Λ :=
      mul_le_mul_of_nonneg_left hlogw (Nat.cast_nonneg m)
    have h₃ : (n : ℝ) * log⁺ ‖w‖ ≤ n * Λ :=
      mul_le_mul_of_nonneg_left hlogw (Nat.cast_nonneg n)
    have h₄ : ((p : ℝ) - q) * Λ + m * Λ + n * Λ + Λ ≤ (p + m + n + 3) * Λ := by
      have e : (p + m + n + 3) * Λ - (((p : ℝ) - q) * Λ + m * Λ + n * Λ + Λ) = (q + 2) * Λ := by
        ring
      have : 0 ≤ ((q : ℝ) + 2) * Λ := by positivity
      linarith
    have h₅ : Su + Sv + log (m + 1) + log (n + 1) + log 2 ≤ Λ := by rw [hΛ]; linarith
    rw [hpq]
    linarith only [hbez, hU, hV, h₁, h₂, h₃, h₄, h₅]

end Real
