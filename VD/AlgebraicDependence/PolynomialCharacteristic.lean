/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
public import VD.AlgebraicDependence.GrowthClass
public import VD.AlgebraicDependence.MonicRelation

/-!
# Valiron–Mohon'ko for Polynomials — Algebraic Dependence work package D

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §6.

Mathlib target: `Mathlib/Analysis/Complex/ValueDistribution/AlgebraicDependence.lean` (part 2)
or a sibling `ValironMohonko.lean`. Dependencies: package C, the pointwise and divisor
estimates `Real.posLog_norm_sum_mul_pow_le` and `MeromorphicOn.negPart_divisor_sum_mul_pow_le`
from packages A and B, the First Main Theorem (inversion,
`characteristic_sub_characteristic_inv_le`), and the growth classes of `GrowthClass.lean`.

Throughout, `f : ℂ → ℂ` is meromorphic, `a : ℕ → ℂ → ℂ` is a family of meromorphic
coefficients, and `∑ j ∈ range (d + 1), a j * f ^ j` is the polynomial expression of degree
`d` in `f` with coefficients `a 0, …, a d`.

## Main results

- D1, `ValueDistribution.characteristic_polynomial_le`: the upper bound
  `T(r, Σ_{j≤d} a j * f ^ j) ≤ d · T(r, f) + Σ_{j≤d} T(r, a j) + log (d + 1)` for `1 ≤ r`,
  without any nondegeneracy hypothesis.
- D2, `ValueDistribution.nsmul_characteristic_le_characteristic_polynomial`: the lower bound
  `d · T(r, f) ≤ T(r, Σ_{j≤d} a j * f ^ j) + (d² + 1) · Σ_{j≤d} T(r, a j) + c` for `1 ≤ r`,
  with an explicit constant `c`, provided the leading coefficient `a d` is not codiscretely
  zero.
- T3, `ValueDistribution.exists_abs_characteristic_polynomial_sub_le`: the **polynomial
  Valiron–Mohon'ko identity**, two-sided:
  `|T(r, Σ_{j≤d} a j * f ^ j) − d · T(r, f)| ≤ (d² + 1) · Σ_{j≤d} T(r, a j) + c`.
- D3, `ValueDistribution.exists_abs_characteristic_polynomial_sub_mem`: the growth-class form.
  For the little-o class along `volume.cofinite ⊓ atTop` this is Laine's Theorem 2.2.5 for
  polynomials, `T(r, P(f)) = deg P · T(r, f) + S(r, f)` whenever the coefficients of `P` are
  small functions with respect to `f`.

## Implementation notes

The upper bound D1 cannot be obtained by applying `characteristic_sum_top_le` and bounding the
terms separately: that gives the factor `Σ_{j≤d} j = d (d + 1) / 2` instead of `d`. It is
instead integrated from the pointwise estimate `Real.posLog_norm_sum_mul_pow_le` and the divisor
estimate `MeromorphicOn.negPart_divisor_sum_mul_pow_le`, in the manner of package C.

The lower bound D2 divides the relation by the leading coefficient `a d` (legitimate on the
codiscrete set where `a d ≠ 0`) and applies the master inequality T1 to the monic relation
`f ^ d + Σ_{j<d} (a d)⁻¹ * a j * f ^ j = (a d)⁻¹ * Σ_{j≤d} a j * f ^ j`. The First Main
Theorem turns every `T(r, (a d)⁻¹ * u)` into `T(r, u) + T(r, a d) + c_d`. Since T1 weights the
`d` lower coefficients with the factor `d`, the leading coefficient picks up the factor
`d² + 1` (and not the `2d + 1` that a dedicated pointwise estimate with leading coefficient
would give); the resulting constant is of no importance for the applications.
-/

@[expose] public section

open Asymptotics Filter Finset Function Real Set Topology

namespace ValueDistribution

variable {f : ℂ → ℂ} {a : ℕ → ℂ → ℂ} {d : ℕ}

/-- The polynomial expression `Σ_{j≤d} a j * f ^ j` is meromorphic. -/
theorem _root_.Meromorphic.polynomial (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j)) :
    Meromorphic (∑ j ∈ range (d + 1), a j * f ^ j) :=
  Meromorphic.sum fun j _ ↦ (ha j).mul hf.pow

/-!
## The Upper Bound
-/

/-- D1, proximity part: `m(r, Σ_{j≤d} a j * f ^ j) ≤ d · m(r, f) + Σ_{j≤d} m(r, a j) + log (d + 1)`,
the pointwise estimate `Real.posLog_norm_sum_mul_pow_le` integrated over the circle. -/
theorem proximity_polynomial_le (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j)) (r : ℝ) :
    proximity (∑ j ∈ range (d + 1), a j * f ^ j) ⊤ r
      ≤ d * proximity f ⊤ r + ∑ j ∈ range (d + 1), proximity (a j) ⊤ r + log (d + 1) := by
  have hint : ∀ {u : ℂ → ℂ}, Meromorphic u → CircleIntegrable (fun z ↦ log⁺ ‖u z‖) 0 r :=
    fun hu ↦ hu.meromorphicOn.circleIntegrable_posLog_norm
  have hcoef : ∀ j ∈ range (d + 1), CircleIntegrable (fun z ↦ log⁺ ‖a j z‖) 0 r :=
    fun j _ ↦ hint (ha j)
  have hF : CircleIntegrable ((d : ℝ) • fun z ↦ log⁺ ‖f z‖) 0 r :=
    IntervalIntegrable.const_mul (hint hf) _
  have hB := CircleIntegrable.sum (range (d + 1)) hcoef
  have hC : CircleIntegrable (fun _ : ℂ ↦ log ((d : ℝ) + 1)) 0 r := circleIntegrable_const _ _ _
  simp only [proximity_top]
  have key : circleAverage (fun z ↦ log⁺ ‖(∑ j ∈ range (d + 1), a j * f ^ j) z‖) 0 r
      ≤ circleAverage ((d : ℝ) • (fun z ↦ log⁺ ‖f z‖)
          + ∑ j ∈ range (d + 1), (fun z ↦ log⁺ ‖a j z‖) + fun _ ↦ log ((d : ℝ) + 1)) 0 r := by
    apply circleAverage_mono (hint (hf.polynomial ha)) ((hF.add hB).add hC)
    intro z _
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply,
      smul_eq_mul]
    exact posLog_norm_sum_mul_pow_le (fun j ↦ a j z) (f z)
  rwa [circleAverage_add (hF.add hB) hC, circleAverage_add hF hB, circleAverage_smul,
    circleAverage_sum hcoef, circleAverage_const, smul_eq_mul] at key

/-- D1, counting part: `N(r, Σ_{j≤d} a j * f ^ j) ≤ d · N(r, f) + Σ_{j≤d} N(r, a j)`, the divisor
estimate `MeromorphicOn.negPart_divisor_sum_mul_pow_le` at the level of counting functions. -/
theorem logCounting_polynomial_le (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j)) {r : ℝ}
    (hr : 1 ≤ r) :
    logCounting (∑ j ∈ range (d + 1), a j * f ^ j) ⊤ r
      ≤ d * logCounting f ⊤ r + ∑ j ∈ range (d + 1), logCounting (a j) ⊤ r := by
  simp only [logCounting_top]
  have := locallyFinsuppWithin.logCounting_le
    (hf.meromorphicOn.negPart_divisor_sum_mul_pow_le (d := d) fun j ↦ (ha j).meromorphicOn) hr
  simpa [Finset.sum_apply, nsmul_eq_mul, add_comm] using this

/-- **Upper bound for polynomial expressions** (D1):
`T(r, Σ_{j≤d} a j * f ^ j) ≤ d · T(r, f) + Σ_{j≤d} T(r, a j) + log (d + 1)` for `1 ≤ r`. No
nondegeneracy hypothesis is needed. -/
theorem characteristic_polynomial_le (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j))
    {r : ℝ} (hr : 1 ≤ r) :
    characteristic (∑ j ∈ range (d + 1), a j * f ^ j) ⊤ r
      ≤ d * characteristic f ⊤ r + ∑ j ∈ range (d + 1), characteristic (a j) ⊤ r
        + log (d + 1) := by
  simp only [characteristic, Pi.add_apply, Finset.sum_add_distrib]
  linarith [proximity_polynomial_le (d := d) hf ha r, logCounting_polynomial_le (d := d) hf ha hr]

/-!
## The Lower Bound and the Two-Sided Identity
-/

/-- **Lower bound for polynomial expressions** (D2): if the leading coefficient `a d` is not
codiscretely zero, then
`d · T(r, f) ≤ T(r, Σ_{j≤d} a j * f ^ j) + (d² + 1) · Σ_{j≤d} T(r, a j) + c` for `1 ≤ r`, with
the explicit constant
`c = d · log (2 (d + 1)) + (d² + 1) · max |log ‖a d 0‖| |log ‖meromorphicTrailingCoeffAt (a d) 0‖|`.
-/
theorem nsmul_characteristic_le_characteristic_polynomial (hf : Meromorphic f)
    (ha : ∀ j, Meromorphic (a j)) (hd : ¬ a d =ᶠ[codiscrete ℂ] 0) {r : ℝ} (hr : 1 ≤ r) :
    d * characteristic f ⊤ r
      ≤ characteristic (∑ j ∈ range (d + 1), a j * f ^ j) ⊤ r
        + (d ^ 2 + 1) * ∑ j ∈ range (d + 1), characteristic (a j) ⊤ r
        + (d * log (2 * (d + 1))
          + (d ^ 2 + 1) * max |log ‖a d 0‖| |log ‖meromorphicTrailingCoeffAt (a d) 0‖|) := by
  set c := max |log ‖a d 0‖| |log ‖meromorphicTrailingCoeffAt (a d) 0‖| with hc
  -- The leading coefficient does not vanish on a codiscrete set.
  have hne : ∀ᶠ z in codiscrete ℂ, a d z ≠ 0 := by
    have h : ∀ z, meromorphicOrderAt (a d) z ≠ ⊤ := by
      have := (ha d).exists_meromorphicOrderAt_eq_top_iff_eventually_zero.not.2 hd
      push Not at this
      exact this
    exact (ha d).meromorphicOn.eventually_codiscreteWithin_apply_ne_zero fun z _ ↦ h z
  -- Dividing by it produces a monic relation.
  have hrel : f ^ d + ∑ j ∈ range d, ((a d)⁻¹ * a j) * f ^ j
      =ᶠ[codiscrete ℂ] (a d)⁻¹ * ∑ j ∈ range (d + 1), a j * f ^ j := by
    filter_upwards [hne] with z hz
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, Finset.sum_apply,
      sum_range_succ, mul_add, mul_sum, mul_assoc]
    rw [inv_mul_cancel_left₀ hz, add_comm]
  -- The master inequality for the monic relation.
  have h₁ := nsmul_characteristic_le_of_monic_eq hf (fun j ↦ (ha d).inv.mul (ha j)) hrel hr
  -- The First Main Theorem removes the inverse of the leading coefficient.
  have hinv : characteristic (a d)⁻¹ ⊤ r ≤ characteristic (a d) ⊤ r + c :=
    by linarith [(abs_le.1 (characteristic_sub_characteristic_inv_le (ha d) (R := r))).1]
  have hmul : ∀ {u : ℂ → ℂ}, Meromorphic u →
      characteristic ((a d)⁻¹ * u) ⊤ r ≤ characteristic u ⊤ r + (characteristic (a d) ⊤ r + c) :=
    fun hu ↦ by linarith [characteristic_mul_top_le' hr (ha d).inv hu]
  have hsum : ∑ j ∈ range d, characteristic ((a d)⁻¹ * a j) ⊤ r
      ≤ ∑ j ∈ range d, characteristic (a j) ⊤ r + d * (characteristic (a d) ⊤ r + c) := by
    calc ∑ j ∈ range d, characteristic ((a d)⁻¹ * a j) ⊤ r
        ≤ ∑ j ∈ range d, (characteristic (a j) ⊤ r + (characteristic (a d) ⊤ r + c)) :=
          sum_le_sum fun j _ ↦ hmul (ha j)
      _ = _ := by rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  -- Collecting the constants.
  have hd₀ : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hS₀ : 0 ≤ ∑ j ∈ range d, characteristic (a j) ⊤ r :=
    sum_nonneg fun j _ ↦ characteristic_nonneg hr
  have hdS : (d : ℝ) * ∑ j ∈ range d, characteristic (a j) ⊤ r
      ≤ (d ^ 2 + 1) * ∑ j ∈ range d, characteristic (a j) ⊤ r :=
    mul_le_mul_of_nonneg_right (by nlinarith) hS₀
  have hdsum := mul_le_mul_of_nonneg_left hsum hd₀
  have hh := hmul (hf.polynomial ha (d := d))
  have hsplit : ∑ j ∈ range (d + 1), characteristic (a j) ⊤ r
      = ∑ j ∈ range d, characteristic (a j) ⊤ r + characteristic (a d) ⊤ r := sum_range_succ _ _
  rw [hsplit]
  linarith

/-- **The polynomial Valiron–Mohon'ko identity** (T3): if the leading coefficient `a d` is not
codiscretely zero, then `T(r, Σ_{j≤d} a j * f ^ j) = d · T(r, f) + O(Σ_{j≤d} T(r, a j)) + O(1)`,
with explicit constants:
`|T(r, Σ_{j≤d} a j * f ^ j) − d · T(r, f)| ≤ (d² + 1) · Σ_{j≤d} T(r, a j) + c` for all `1 ≤ r`.
-/
theorem exists_abs_characteristic_polynomial_sub_le (hf : Meromorphic f)
    (ha : ∀ j, Meromorphic (a j)) (hd : ¬ a d =ᶠ[codiscrete ℂ] 0) :
    ∃ c, ∀ r, 1 ≤ r →
      |characteristic (∑ j ∈ range (d + 1), a j * f ^ j) ⊤ r - d * characteristic f ⊤ r|
        ≤ (d ^ 2 + 1) * ∑ j ∈ range (d + 1), characteristic (a j) ⊤ r + c := by
  refine ⟨log (d + 1) + (d * log (2 * (d + 1))
    + (d ^ 2 + 1) * max |log ‖a d 0‖| |log ‖meromorphicTrailingCoeffAt (a d) 0‖|), fun r hr ↦ ?_⟩
  have hS₀ : 0 ≤ ∑ j ∈ range (d + 1), characteristic (a j) ⊤ r :=
    sum_nonneg fun j _ ↦ characteristic_nonneg hr
  have hd₀ : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hlog₁ : 0 ≤ log ((d : ℝ) + 1) := log_nonneg (by linarith)
  have hlog₂ : 0 ≤ (d : ℝ) * log (2 * (d + 1)) :=
    mul_nonneg hd₀ (log_nonneg (by linarith))
  have hc₀ : 0 ≤ (d ^ 2 + 1 : ℝ)
      * max |log ‖a d 0‖| |log ‖meromorphicTrailingCoeffAt (a d) 0‖| :=
    mul_nonneg (by positivity) (le_max_of_le_left (abs_nonneg _))
  have hS : ∑ j ∈ range (d + 1), characteristic (a j) ⊤ r
      ≤ (d ^ 2 + 1) * ∑ j ∈ range (d + 1), characteristic (a j) ⊤ r :=
    le_mul_of_one_le_left hS₀ (by nlinarith)
  rw [abs_le]
  constructor
  · linarith [nsmul_characteristic_le_characteristic_polynomial hf ha hd hr]
  · linarith [characteristic_polynomial_le (d := d) hf ha hr]

/-!
## The Growth-Class Form
-/

/-- **Valiron–Mohon'ko for polynomials with coefficients in a growth class** (D3): if the
coefficients `a j` have characteristic in the growth class `G` and the leading coefficient is
not codiscretely zero, then `T(r, Σ_{j≤d} a j * f ^ j) = d · T(r, f) + u(r)` with `u ∈ G`. For
the little-o class `(· =o[volume.cofinite ⊓ atTop] T(r, f))` this is Laine's Theorem 2.2.5 for
polynomials: `T(r, P(f)) = deg P · T(r, f) + S(r, f)`. -/
theorem exists_abs_characteristic_polynomial_sub_mem {l : Filter ℝ} {G : (ℝ → ℝ) → Prop}
    (hG : IsGrowthClass l G) (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j))
    (ha' : ∀ j ∈ range (d + 1), G (characteristic (a j) ⊤)) (hd : ¬ a d =ᶠ[codiscrete ℂ] 0) :
    ∃ u, G u ∧ ∀ᶠ r in l,
      |characteristic (∑ j ∈ range (d + 1), a j * f ^ j) ⊤ r - d * characteristic f ⊤ r|
        ≤ u r := by
  obtain ⟨c, hc⟩ := exists_abs_characteristic_polynomial_sub_le hf ha hd
  refine ⟨(d ^ 2 + 1) • ∑ j ∈ range (d + 1), characteristic (a j) ⊤ + fun _ ↦ c,
    hG.add (hG.nsmul (hG.sum ha') _) (hG.const c), ?_⟩
  filter_upwards [hG.le_atTop (eventually_ge_atTop 1)] with r hr
  simpa [Finset.sum_apply, nsmul_eq_mul] using hc r hr

end ValueDistribution
