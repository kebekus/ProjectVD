/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.BorelGrowth
import VD.LLD.LogDerivTwoRadius

/-!
# The Lemma on the Logarithmic Derivative — LLD work package E (theorem T3)

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §7.

Mathlib target: `Mathlib/Analysis/Complex/ValueDistribution/LogDerivLemma.lean` (part 2).
Dependencies: `BorelGrowth.lean`, `LogDerivTwoRadius.lean`.

This file proves **Nevanlinna's Lemma on the Logarithmic Derivative**: for a meromorphic
function `f` on the complex plane (no nondegeneracy hypothesis needed),

```
proximity (logDeriv f) ⊤ =O[volume.cofinite ⊓ atTop]
  fun r ↦ log⁺ (characteristic f ⊤ r) + log r,
```

that is, `m(r, f'/f) = O(log⁺ T(r, f) + log r)` for all large `r` outside a set of finite
Lebesgue measure. This is the key analytic input for the Second Main Theorem of value
distribution theory. References: [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677],
Ch. VI; [Hayman, *Meromorphic Functions*][MR164038], §3.1.

The proof combines the two-radius estimate (theorem T1,
`ValueDistribution.exists_proximity_logDeriv_le`) with Borel's growth lemma (theorem T2,
`MonotoneOn.eventually_le_two_mul`): apply T1 with the enlarged radius `R := r + (S r)⁻¹`,
where `S r := max 1 (characteristic f ⊤ r)`; then `log⁺ (R - r)⁻¹ = log⁺ (characteristic f ⊤ r)`
exactly, and the Borel lemma controls `characteristic f ⊤ R` by `2 * S r` away from an
exceptional set of finite measure.

For functions of **finite order**, the exceptional set can be avoided entirely
(`ValueDistribution.isBigO_proximity_logDeriv_of_isBigO_rpow`): applying T1 with `R := 2 * r`
gives `proximity (logDeriv f) ⊤ =O[atTop] Real.log` whenever
`characteristic f ⊤ =O[atTop] (· ^ ρ)`. The Borel lemma is not needed there.
-/

open Asymptotics Complex Filter MeasureTheory Metric Real Set ValueDistribution

/-!
## Preliminaries
-/

/-- Variant of the two-radius estimate with a nonnegative constant. -/
private lemma exists_nonneg_proximity_logDeriv_le {f : ℂ → ℂ} (hf : Meromorphic f) :
    ∃ c, 0 ≤ c ∧ ∀ r R : ℝ, 1 ≤ r → r < R →
      proximity (logDeriv f) ⊤ r
        ≤ c * (log⁺ (characteristic f ⊤ R) + Real.log R + log⁺ (R - r)⁻¹ + 1) := by
  obtain ⟨c₀, hc₀⟩ := exists_proximity_logDeriv_le hf
  refine ⟨max c₀ 0, le_max_right _ _, fun r R hr hrR ↦ ?_⟩
  refine (hc₀ r R hr hrR).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  have h₁ := posLog_nonneg (x := characteristic f ⊤ R)
  have h₂ := posLog_nonneg (x := (R - r)⁻¹)
  have h₃ : (0:ℝ) ≤ Real.log R := Real.log_nonneg (by linarith)
  linarith

/-!
## The Lemma on the Logarithmic Derivative
-/

/-- **Nevanlinna's Lemma on the Logarithmic Derivative**: for a meromorphic function `f` on the
complex plane, the proximity function of `logDeriv f = f'/f` for the value `⊤` satisfies
`m(r, f'/f) = O(log⁺ T(r, f) + log r)` as `r → ∞`, outside an exceptional set of finite
Lebesgue measure. -/
theorem ValueDistribution.isBigO_proximity_logDeriv {f : ℂ → ℂ} (hf : Meromorphic f) :
    proximity (logDeriv f) ⊤ =O[volume.cofinite ⊓ atTop]
      fun r ↦ log⁺ (characteristic f ⊤ r) + Real.log r := by
  obtain ⟨c, hc₁, hc⟩ := exists_nonneg_proximity_logDeriv_le hf
  -- The comparison function `S`, monotone and `≥ 1`
  set S : ℝ → ℝ := fun r ↦ max 1 (characteristic f ⊤ r) with hS_def
  have hS1 : ∀ r, 1 ≤ S r := fun r ↦ le_max_left _ _
  have hSpos : ∀ r, 0 < S r := fun r ↦ lt_of_lt_of_le one_pos (hS1 r)
  have hSmono : MonotoneOn S (Ici 1) := fun x hx y hy hxy ↦
    max_le_max le_rfl (characteristic_monotoneOn hf (mem_Ioi.2 (lt_of_lt_of_le one_pos hx))
      (mem_Ioi.2 (lt_of_lt_of_le one_pos hy)) hxy)
  -- Borel's growth lemma (T2)
  have hBorel := hSmono.eventually_le_two_mul (hSpos 1).le
  rw [isBigO_iff]
  refine ⟨c * (3 + 2 * Real.log 2), ?_⟩
  filter_upwards [hBorel, mem_inf_of_right (eventually_ge_atTop (Real.exp 1))] with r hBor hre
  have hexp1 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hr1 : (1:ℝ) ≤ r := by linarith
  have hlogr : 1 ≤ Real.log r := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hre
  have hT₀r : 0 ≤ characteristic f ⊤ r := characteristic_nonneg hr1
  -- Apply the two-radius estimate (T1) with `R := r + (S r)⁻¹`
  have hrR : r < r + (S r)⁻¹ := lt_add_of_pos_right _ (inv_pos.2 (hSpos r))
  have hRle : r + (S r)⁻¹ ≤ 2 * r := by
    have h₁ : (S r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hS1 r)
    linarith
  have h₁ := hc r (r + (S r)⁻¹) hr1 hrR
  have hT₀R : 0 ≤ characteristic f ⊤ (r + (S r)⁻¹) := characteristic_nonneg (by linarith)
  -- The error term equals `log⁺` of the characteristic
  have eS : log⁺ (S r) = log⁺ (characteristic f ⊤ r) := by
    calc log⁺ (S r)
        = Real.log (S r) := posLog_eq_log (by rw [abs_of_pos (hSpos r)]; exact hS1 r)
      _ = log⁺ (characteristic f ⊤ r) := (posLog_eq_log_max_one hT₀r).symm
  have e₁ : log⁺ (r + (S r)⁻¹ - r)⁻¹ = log⁺ (characteristic f ⊤ r) := by
    rw [add_sub_cancel_left, inv_inv, eS]
  -- The radius term
  have e₂ : Real.log (r + (S r)⁻¹) ≤ Real.log 2 + Real.log r := by
    calc Real.log (r + (S r)⁻¹)
        ≤ Real.log (2 * r) := Real.log_le_log (by linarith) hRle
      _ = Real.log 2 + Real.log r := Real.log_mul two_ne_zero (by linarith)
  -- The characteristic at the enlarged radius, controlled by Borel's lemma
  have e₃ : log⁺ (characteristic f ⊤ (r + (S r)⁻¹))
      ≤ Real.log 2 + log⁺ (characteristic f ⊤ r) := by
    have h₂ : characteristic f ⊤ (r + (S r)⁻¹) ≤ 2 * S r :=
      le_trans (le_max_right _ _) hBor
    calc log⁺ (characteristic f ⊤ (r + (S r)⁻¹))
        ≤ log⁺ (2 * S r) := posLog_le_posLog (neg_one_lt_zero.le.trans hT₀R) h₂
      _ ≤ log⁺ 2 + log⁺ (S r) := posLog_mul
      _ ≤ Real.log 2 + log⁺ (characteristic f ⊤ r) := by
          rw [posLog_eq_log (by norm_num), eS]
  -- Assemble
  rw [Real.norm_eq_abs, abs_of_nonneg (proximity_nonneg r), Real.norm_eq_abs,
    abs_of_nonneg (by linarith [posLog_nonneg (x := characteristic f ⊤ r)])]
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hbr : log⁺ (characteristic f ⊤ (r + (S r)⁻¹)) + Real.log (r + (S r)⁻¹)
        + log⁺ (r + (S r)⁻¹ - r)⁻¹ + 1
      ≤ (3 + 2 * Real.log 2) * (log⁺ (characteristic f ⊤ r) + Real.log r) := by
    rw [e₁]
    nlinarith [e₂, e₃, posLog_nonneg (x := characteristic f ⊤ r),
      mul_nonneg hlog2 (posLog_nonneg (x := characteristic f ⊤ r)),
      mul_nonneg hlog2 (by linarith : (0:ℝ) ≤ Real.log r - 1)]
  calc proximity (logDeriv f) ⊤ r
      ≤ c * (log⁺ (characteristic f ⊤ (r + (S r)⁻¹)) + Real.log (r + (S r)⁻¹)
          + log⁺ (r + (S r)⁻¹ - r)⁻¹ + 1) := h₁
    _ ≤ c * ((3 + 2 * Real.log 2) * (log⁺ (characteristic f ⊤ r) + Real.log r)) :=
        mul_le_mul_of_nonneg_left hbr hc₁
    _ = c * (3 + 2 * Real.log 2) * (log⁺ (characteristic f ⊤ r) + Real.log r) :=
        (mul_assoc _ _ _).symm

/-!
## Functions of Finite Order

For functions of finite order, the Lemma on the Logarithmic Derivative holds with **no
exceptional set**: taking `R := 2 * r` in the two-radius estimate suffices, and the Borel
growth lemma is not needed.
-/

/-- **Lemma on the Logarithmic Derivative, finite-order case**: if the characteristic function
of a meromorphic function `f` grows at most like a power of the radius, then
`m(r, f'/f) = O(log r)` as `r → ∞`, with no exceptional set. -/
theorem ValueDistribution.isBigO_proximity_logDeriv_of_isBigO_rpow {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Meromorphic f) (h : characteristic f ⊤ =O[atTop] (· ^ ρ)) :
    proximity (logDeriv f) ⊤ =O[atTop] Real.log := by
  obtain ⟨c, hc₁, hc⟩ := exists_nonneg_proximity_logDeriv_le hf
  -- Upgrade the growth hypothesis to a nonnegative exponent
  set p := max ρ 0 with hp_def
  have hp₀ : 0 ≤ p := le_max_right _ _
  have h' : characteristic f ⊤ =O[atTop] (· ^ p) := by
    apply h.trans
    rw [isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx₀ : (0:ℝ) < x := by linarith
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx₀.le _), abs_of_nonneg (Real.rpow_nonneg hx₀.le _)]
    exact Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
  -- Extract an eventual bound with a nonnegative constant
  obtain ⟨C, hC⟩ := isBigO_iff.1 h'
  have hC' : ∀ᶠ s in atTop, characteristic f ⊤ s ≤ |C| * s ^ p := by
    filter_upwards [hC, eventually_ge_atTop 1] with s hs hs1
    have hs₀ : (0:ℝ) < s := by linarith
    calc characteristic f ⊤ s
        ≤ |characteristic f ⊤ s| := le_abs_self _
      _ ≤ C * ‖s ^ p‖ := hs
      _ ≤ |C| * s ^ p := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hs₀.le _)]
          exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hs₀.le _)
  -- Transport the bound to the radius `2 * r`
  have h2r : Tendsto (fun r : ℝ ↦ 2 * r) atTop atTop :=
    Tendsto.const_mul_atTop two_pos tendsto_id
  have hT2 : ∀ᶠ r in atTop, characteristic f ⊤ (2 * r) ≤ |C| * (2 * r) ^ p :=
    h2r.eventually hC'
  -- Assemble
  rw [isBigO_iff]
  refine ⟨c * (log⁺ |C| + p * Real.log 2 + Real.log 2 + 2 + p), ?_⟩
  filter_upwards [hT2, eventually_ge_atTop (Real.exp 1)] with r hT2r hre
  have hexp1 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hr1 : (1:ℝ) ≤ r := by linarith
  have hlogr : 1 ≤ Real.log r := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hre
  -- Apply the two-radius estimate (T1) with `R := 2 * r`
  have h₁ := hc r (2 * r) hr1 (by linarith)
  have hT₀ : 0 ≤ characteristic f ⊤ (2 * r) := characteristic_nonneg (by linarith)
  -- The error term vanishes
  have e₁ : log⁺ (2 * r - r)⁻¹ = 0 := by
    rw [show 2 * r - r = r by ring]
    apply (posLog_eq_zero_iff _).2
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ hr1
  -- The radius term
  have e₂ : Real.log (2 * r) = Real.log 2 + Real.log r := Real.log_mul two_ne_zero (by linarith)
  -- The characteristic term, via the growth hypothesis
  have e₃ : log⁺ (characteristic f ⊤ (2 * r))
      ≤ log⁺ |C| + p * (Real.log 2 + Real.log r) := by
    calc log⁺ (characteristic f ⊤ (2 * r))
        ≤ log⁺ (|C| * (2 * r) ^ p) := posLog_le_posLog (neg_one_lt_zero.le.trans hT₀) hT2r
      _ ≤ log⁺ |C| + log⁺ ((2 * r) ^ p) := posLog_mul
      _ = log⁺ |C| + p * log⁺ (2 * r) := by
            rw [posLog_rpow (neg_one_lt_zero.le.trans (by positivity)) hp₀]
      _ ≤ log⁺ |C| + p * (Real.log 2 + Real.log r) := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hp₀)
          rw [posLog_eq_log (by rw [abs_of_pos (by positivity)]; linarith), e₂]
  -- Final numeric assembly
  rw [Real.norm_eq_abs, abs_of_nonneg (proximity_nonneg r), Real.norm_eq_abs,
    abs_of_nonneg (show (0:ℝ) ≤ Real.log r by linarith)]
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hbr : log⁺ (characteristic f ⊤ (2 * r)) + Real.log (2 * r) + log⁺ (2 * r - r)⁻¹ + 1
      ≤ (log⁺ |C| + p * Real.log 2 + Real.log 2 + 2 + p) * Real.log r := by
    rw [e₁, e₂]
    nlinarith [e₃, posLog_nonneg (x := |C|),
      mul_nonneg (posLog_nonneg (x := |C|)) (by linarith : (0:ℝ) ≤ Real.log r - 1),
      mul_nonneg (mul_nonneg hp₀ hlog2) (by linarith : (0:ℝ) ≤ Real.log r - 1),
      mul_nonneg hlog2 (by linarith : (0:ℝ) ≤ Real.log r - 1),
      mul_nonneg hp₀ (by linarith : (0:ℝ) ≤ Real.log r - 1)]
  calc proximity (logDeriv f) ⊤ r
      ≤ c * (log⁺ (characteristic f ⊤ (2 * r)) + Real.log (2 * r)
          + log⁺ (2 * r - r)⁻¹ + 1) := h₁
    _ ≤ c * ((log⁺ |C| + p * Real.log 2 + Real.log 2 + 2 + p) * Real.log r) :=
        mul_le_mul_of_nonneg_left hbr hc₁
    _ = c * (log⁺ |C| + p * Real.log 2 + Real.log 2 + 2 + p) * Real.log r :=
        (mul_assoc _ _ _).symm

/-!
## Sanity Check

For `f = Complex.exp`, the logarithmic derivative is the constant function `1`, and the
proximity function on the left-hand side of the Lemma on the Logarithmic Derivative vanishes
identically.
-/

example (r : ℝ) : proximity (logDeriv Complex.exp) ⊤ r = 0 := by
  rw [Complex.logDeriv_exp, proximity_top]
  have h₁ : (fun x ↦ log⁺ ‖(1 : ℂ → ℂ) x‖) = fun _ ↦ (0:ℝ) := by
    funext x
    simp [posLog]
  rw [h₁, circleAverage_const]
