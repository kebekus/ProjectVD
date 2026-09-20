/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CanonicalDecomposition

/-!
# Further API for the Canonical Factor

Submitted to Mathlib as PR #43985 (draft), "feat: API for working with canonical
decompositions", https://github.com/leanprover-community/mathlib4/pull/43985.

Mathlib target: `Mathlib/Analysis/Complex/CanonicalDecomposition.lean`. In the submitted version,
`one_lt_norm_canonicalFactor` sits in the existing section "Canonical Factors", directly after
`norm_canonicalFactor_eval_circle_eq_one`, and the two `logDeriv` lemmas form the new subsection
"The Logarithmic Derivative" after "Orders and Divisors". The target file gains the import
`Mathlib.Analysis.Calculus.LogDeriv`, which costs nothing: `LogDeriv` already sits below that file
in the import graph, and no Mathlib file imports
`Mathlib.Analysis.Complex.CanonicalDecomposition`. The declarations below are the submitted text,
except that there `R` and `w` come from the target file's `variable` block and the redundant
`Complex.` prefixes are dropped.

Once the PR is merged, delete this file and remove the import from
`VD/LLD/PoissonSchwarzDeriv.lean` and `VD/MathlibPending/ProximityBounded.lean`, which then receive
the lemmas transitively through `Mathlib/Analysis/Complex/CanonicalDecomposition.lean`.

## Main results

- `Complex.one_lt_norm_canonicalFactor`: the canonical factor has norm strictly greater than one at
  every point of the open ball other than its pole.
- `Complex.logDeriv_canonicalFactor`: the logarithmic derivative of the canonical factor, away from
  its zero and pole.
- `Complex.norm_logDeriv_canonicalFactor_le`: the bound `‖z - w‖⁻¹ + (R - r)⁻¹` for the norm of the
  logarithmic derivative on interior circles. This is the form in which the estimate enters the
  two-radius estimate for the Lemma on the Logarithmic Derivative.
-/

open Metric Set

open scoped ComplexConjugate

namespace Complex

/-!
## The Canonical Factor on the Open Ball
-/

/-- The canonical factor `canonicalFactor R w` has norm strictly greater than one at every
point `z` of the open ball `ball 0 R` other than its pole `w`. -/
theorem one_lt_norm_canonicalFactor {R : ℝ} {w z : ℂ} (hw : w ∈ ball 0 R) (hz : z ∈ ball 0 R)
    (hzw : z ≠ w) :
    1 < ‖canonicalFactor R w z‖ := by
  have hR : 0 < R := pos_of_mem_ball hw
  rw [mem_ball_zero_iff] at hw hz
  have hd : (R : ℂ) * (z - w) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 hR.ne') (sub_ne_zero.2 hzw)
  -- The classical identity `‖R² - conj w * z‖² - ‖R * (z - w)‖² = (R² - ‖w‖²) * (R² - ‖z‖²)`,
  -- whose right-hand side is positive inside the ball.
  have key : ‖(R : ℂ) * (z - w)‖ < ‖(R : ℂ) ^ 2 - conj w * z‖ := by
    have hid : ‖(R : ℂ) ^ 2 - conj w * z‖ ^ 2 - ‖(R : ℂ) * (z - w)‖ ^ 2
        = (R ^ 2 - ‖w‖ ^ 2) * (R ^ 2 - ‖z‖ ^ 2) := by
      simp only [← normSq_eq_norm_sq, ← ofReal_pow, normSq_apply, sub_re, sub_im, mul_re, mul_im,
        conj_re, conj_im, ofReal_re, ofReal_im]
      ring
    have hpos : 0 < ‖(R : ℂ) ^ 2 - conj w * z‖ ^ 2 - ‖(R : ℂ) * (z - w)‖ ^ 2 := by
      rw [hid]
      have h₁ : ‖w‖ ^ 2 < R ^ 2 := by nlinarith [norm_nonneg w]
      have h₂ : ‖z‖ ^ 2 < R ^ 2 := by nlinarith [norm_nonneg z]
      exact mul_pos (by linarith) (by linarith)
    nlinarith [norm_nonneg ((R : ℂ) * (z - w)), norm_nonneg ((R : ℂ) ^ 2 - conj w * z), hpos]
  rwa [canonicalFactor_apply, norm_div, one_lt_div (norm_pos_iff.2 hd)]

/-!
## The Logarithmic Derivative of the Canonical Factor
-/

/-- The logarithmic derivative of the canonical factor, away from its zero and pole. -/
theorem logDeriv_canonicalFactor {R : ℝ} {w z : ℂ} (hR : R ≠ 0) (h₁z : z ≠ w)
    (h₂z : R ^ 2 - conj w * z ≠ 0) :
    logDeriv (canonicalFactor R w) z = -((z - w)⁻¹ + conj w / (R ^ 2 - conj w * z)) := by
  have h₁ : HasDerivAt (fun x : ℂ ↦ R ^ 2 - conj w * x) (-conj w) z := by
    simpa using ((hasDerivAt_id z).const_mul (conj w)).const_sub ((R : ℂ) ^ 2)
  have h₂ : HasDerivAt (fun x : ℂ ↦ R * (x - w)) (R * 1) z :=
    ((hasDerivAt_id z).sub_const w).const_mul _
  have h₃ : (R : ℂ) * (z - w) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 hR) (sub_ne_zero.2 h₁z)
  rw [canonicalFactor_def,
    logDeriv_fun_div z h₂z h₃ h₁.differentiableAt h₂.differentiableAt,
    logDeriv_const_mul z _ (Complex.ofReal_ne_zero.2 hR)]
  have h₄ : HasDerivAt (· - w) 1 z := by
    simpa using (hasDerivAt_id z).sub_const w
  rw [logDeriv_apply, logDeriv_apply, h₁.deriv, h₄.deriv, neg_div]
  field_simp [sub_ne_zero.2 h₁z]
  ring

/--
Norm bound for the logarithmic derivative of the canonical factor on interior circles: for `‖w‖ < R`
and `‖z‖ = r < R`, we have `‖logDeriv (canonicalFactor R w) z‖ ≤ ‖z - w‖⁻¹ + (R - r)⁻¹`.
-/
theorem norm_logDeriv_canonicalFactor_le {R r : ℝ} {w z : ℂ}
    (hw : ‖w‖ < R) (hz : ‖z‖ = r) (hr : r < R) :
    ‖logDeriv (canonicalFactor R w) z‖ ≤ ‖z - w‖⁻¹ + (R - r)⁻¹ := by
  have hr₀ : 0 ≤ r := hz ▸ norm_nonneg z
  have hR : 0 < R := lt_of_le_of_lt hr₀ hr
  rcases eq_or_ne z w with rfl | h₁z
  · rw [logDeriv_apply, canonicalFactor_apply_self, div_zero, norm_zero]
    exact add_nonneg (inv_nonneg.2 (norm_nonneg _)) (inv_nonneg.2 (by linarith))
  · have h₂z : (R : ℂ) ^ 2 - conj w * z ≠ 0 := by
      intro hcon
      have h₁ : ‖((R : ℂ) ^ 2)‖ = ‖conj w * z‖ := by rw [sub_eq_zero.1 hcon]
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, norm_mul,
        Complex.norm_conj, hz] at h₁
      nlinarith
    rw [logDeriv_canonicalFactor hR.ne' h₁z h₂z, norm_neg]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_inv]
    gcongr
    -- ‖conj w / (R² - conj w * z)‖ ≤ (R - r)⁻¹
    rw [norm_div, Complex.norm_conj]
    have hD : R ^ 2 - ‖w‖ * r ≤ ‖(R : ℂ) ^ 2 - conj w * z‖ := by
      have h₁ := norm_sub_norm_le ((R : ℂ) ^ 2) (conj w * z)
      rwa [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, norm_mul,
        Complex.norm_conj, hz] at h₁
    have hD₀ : 0 < R ^ 2 - ‖w‖ * r := by nlinarith [norm_nonneg w]
    calc ‖w‖ / ‖(R : ℂ) ^ 2 - conj w * z‖
        ≤ ‖w‖ / (R ^ 2 - ‖w‖ * r) := by gcongr
      _ ≤ (R - r)⁻¹ := by
          rw [← one_div, div_le_div_iff₀ hD₀ (by linarith)]
          nlinarith [norm_nonneg w]

end Complex
