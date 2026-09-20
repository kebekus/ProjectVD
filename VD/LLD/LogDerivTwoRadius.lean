/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.Cartan
import VD.LLD.LogDerivEstimates
import VD.LLD.PoissonJensenDeriv

/-!
# The Two-Radius Estimate — LLD work package C4 (theorem T1)

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §5.

Mathlib target: `Mathlib/Analysis/Complex/ValueDistribution/LogDerivLemma.lean` (part 1).
Dependencies: `PoissonJensenDeriv.lean` (the pointwise estimate
`MeromorphicOn.eventually_norm_logDeriv_le`) and `LogDerivEstimates.lean` (the exponent-`1/2`
trick and the comparison lemmas for the value distribution functions).

This file proves the **two-radius estimate** for the Lemma on the Logarithmic Derivative,
`ValueDistribution.exists_proximity_logDeriv_le`: for every meromorphic function `f` on the
complex plane there exists a constant `c ≥ 0` such that for all radii `1 ≤ r < R`,

```
proximity (logDeriv f) ⊤ r ≤ c * (log⁺ (characteristic f ⊤ R) + log R + log⁺ (R - r)⁻¹ + 1).
```

The statement is fully exceptional-set-free; it is the analytic core of the Lemma on the
Logarithmic Derivative. The proof runs along the classical Nevanlinna route, with the
intermediate radius `ρ := (r + R) / 2`:

1. The differentiated Poisson–Jensen formula gives, away from a discrete subset of the circle
   `|w| = r`, the pointwise bound `‖logDeriv f w‖ ≤ K + ∑ |D a| * (‖w - a‖⁻¹ + (ρ - r)⁻¹)`,
   where `K` is a kernel constant controlled by the circle average `A` of `|log ‖f ·‖|` at radius
   `ρ`, and `D` is the divisor of `f` on `ball 0 ρ` (`MeromorphicOn.eventually_norm_logDeriv_le`).
2. The exponent-`1/2` trick bounds `proximity (logDeriv f) ⊤ r` by `log⁺` of the kernel constant
   and `log⁺` of the total mass `N` of `D`
   (`circleAverage_posLog_norm_le_of_le_add_sum_inv_norm_sub`).
3. `A` is bounded by `2 * characteristic f ⊤ R + O_f(1)` using the First Main Theorem
   (`circleAverage_abs_log_norm_le`), and `N` by the counting estimate and the First Main Theorem
   (`finsum_abs_divisor_le`).
4. Collecting the `log⁺` terms gives the theorem.

The degenerate case where `f` vanishes away from a discrete set is handled separately: there,
`logDeriv f` vanishes away from a discrete set and the proximity function is zero.
-/

open Complex Filter Function MeromorphicOn Metric Real Set Topology ValueDistribution

/-!
## The Kernel Constant

The circle average of `|log ‖f ·‖|` at radius `ρ` is bounded by the characteristic function at any
radius `R ≥ ρ`, using the First Main Theorem and monotonicity of the characteristic.
-/

private lemma circleAverage_abs_log_norm_le {f : ℂ → ℂ} {ρ R : ℝ} (hf : Meromorphic f)
    (hρ : 1 ≤ ρ) (hρR : ρ ≤ R) :
    circleAverage (fun ζ ↦ |Real.log ‖f ζ‖|) 0 ρ
      ≤ 2 * characteristic f ⊤ R
        + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have h₁ := congrFun (proximity_add_proximity_inv_eq_circleAverage hf) ρ
  have h₂ := proximity_le_characteristic (f := f) (a := ⊤) hρ
  have h₃ := proximity_le_characteristic (f := f⁻¹) (a := ⊤) hρ
  have h₄ := (abs_le.1 (characteristic_sub_characteristic_inv_le hf (R := ρ))).1
  have h₅ : characteristic f ⊤ ρ ≤ characteristic f ⊤ R :=
    characteristic_monotoneOn hf (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith)) hρR
  simp only [Pi.add_apply] at h₁
  linarith

/-!
## The Divisor Mass

The total mass of the divisor of `f` on `ball 0 ρ`, weighted by `R - ρ`, is bounded by the
characteristic function at radius `R`, using the counting estimate and the First Main Theorem.
-/

private lemma finsum_abs_divisor_le {f : ℂ → ℂ} {ρ R : ℝ} (hf : Meromorphic f)
    (hρ : 1 ≤ ρ) (hρR : ρ < R) :
    (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) * (R - ρ)
      ≤ R * (2 * characteristic f ⊤ R
        + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) := by
  have hρ₀ : (0 : ℝ) < ρ := by linarith
  have hR₀ : (0 : ℝ) < R := by linarith
  have hN₀ : 0 ≤ ∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ) := finsum_nonneg fun a ↦ abs_nonneg _
  -- The counting estimate
  have h₁ := finsum_abs_divisor_ball_mul_log_le hf hρ hρR
  -- `(R - ρ) / R ≤ log (R / ρ)`
  have h₂ : R - ρ ≤ Real.log (R / ρ) * R := by
    rw [← div_le_iff₀ hR₀, sub_div, div_self hR₀.ne']
    simpa [inv_div] using Real.one_sub_inv_le_log_of_pos (div_pos hR₀ hρ₀)
  -- The First Main Theorem
  have h₃ : logCounting f ⊤ R ≤ characteristic f ⊤ R := logCounting_le_characteristic
  have h₄ : logCounting f 0 R ≤ characteristic f ⊤ R
      + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
    have h₅ : logCounting f⁻¹ ⊤ R ≤ characteristic f⁻¹ ⊤ R := logCounting_le_characteristic
    have h₆ := (abs_le.1 (characteristic_sub_characteristic_inv_le hf (R := R))).1
    rw [← logCounting_inv]
    linarith
  calc (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) * (R - ρ)
      ≤ (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) * (Real.log (R / ρ) * R) := by gcongr
    _ = (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) * Real.log (R / ρ) * R := by ring
    _ ≤ (logCounting f 0 R + logCounting f ⊤ R) * R := by gcongr
    _ ≤ (2 * characteristic f ⊤ R
        + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) * R := by
        gcongr ?_ * _
        linarith
    _ = R * (2 * characteristic f ⊤ R
        + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) := mul_comm _ _

/-!
## The Degenerate Case

If `f` vanishes away from a discrete set, then so does `logDeriv f`, and its proximity function
vanishes.
-/

private lemma proximity_logDeriv_eq_zero {f : ℂ → ℂ} {r : ℝ} (hf : Meromorphic f)
    (hdeg : ∃ u, meromorphicOrderAt f u = ⊤) (hr : r ≠ 0) :
    proximity (logDeriv f) ⊤ r = 0 := by
  have h₁ : logDeriv f =ᶠ[codiscrete ℂ] logDeriv (fun _ ↦ (0 : ℂ)) :=
    logDeriv_congr_codiscrete (hf.exists_meromorphicOrderAt_eq_top_iff_eventually_zero.1 hdeg)
  rw [proximity_congr_codiscrete h₁ hr, logDeriv_const, Pi.zero_def, proximity_const]
  simp

/-!
## The Two-Radius Estimate (Theorem T1)
-/

/-- **Two-radius estimate** for the Lemma on the Logarithmic Derivative, fully
exceptional-set-free: for a meromorphic function `f` on the complex plane, there is a constant
`c ≥ 0` such that for all radii `1 ≤ r < R`, the proximity function of `logDeriv f` at radius `r`
is bounded by `c * (log⁺ (characteristic f ⊤ R) + log R + log⁺ (R - r)⁻¹ + 1)`. -/
theorem ValueDistribution.exists_proximity_logDeriv_le {f : ℂ → ℂ} (hf : Meromorphic f) :
    ∃ c, 0 ≤ c ∧ ∀ r R : ℝ, 1 ≤ r → r < R →
      proximity (logDeriv f) ⊤ r
        ≤ c * (log⁺ (characteristic f ⊤ R) + Real.log R + log⁺ (R - r)⁻¹ + 1) := by
  -- Degenerate case: `f` vanishes away from a discrete set; then the proximity function of
  -- `logDeriv f` vanishes.
  by_cases hdeg : ∃ u, meromorphicOrderAt f u = ⊤
  · refine ⟨1, zero_le_one, fun r R hr hrR ↦ ?_⟩
    rw [proximity_logDeriv_eq_zero hf hdeg (by linarith), one_mul]
    have := posLog_nonneg (x := characteristic f ⊤ R)
    have := posLog_nonneg (x := (R - r)⁻¹)
    have := Real.log_nonneg (by linarith : 1 ≤ R)
    linarith
  -- Main case: the constant
  push Not at hdeg
  set c_f := max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  set C₀ : ℝ := 24 * Real.log 2 + 4 * log⁺ c_f with hC₀_def
  have hC₀ : 0 ≤ C₀ := by
    have := posLog_nonneg (x := c_f)
    linarith
  refine ⟨6 + C₀, by linarith, fun r R hr hrR ↦ ?_⟩
  -- The radii
  set ρ := (r + R) / 2 with hρ_def
  have hrρ : r < ρ := by linarith
  have hρR : ρ < R := by linarith
  have h1ρ : 1 ≤ ρ := by linarith
  have hr₀ : (0 : ℝ) < r := by linarith
  have hρ₀ : (0 : ℝ) < ρ := by linarith
  have hR₀ : (0 : ℝ) < R := by linarith
  have hρr₀ : (0 : ℝ) < ρ - r := by linarith
  have hRr₀ : (0 : ℝ) < R - r := by linarith
  have hρ_r : ρ - r = (R - r) / 2 := by linarith
  have hR_ρ : R - ρ = (R - r) / 2 := by linarith
  -- Abbreviations: the characteristic `T`, the circle average `A` of `|log ‖f ·‖|` at radius
  -- `ρ`, the kernel constant `K`, the pole distance `β`, and the divisor mass `N`
  set T := characteristic f ⊤ R
  set A := circleAverage (fun ζ ↦ |Real.log ‖f ζ‖|) 0 ρ
  set K := 2 * ρ / (ρ - r) ^ 2 * A with hK_def
  set β := (ρ - r)⁻¹ with hβ_def
  have hd_fin : (divisor f (ball 0 ρ)).support.Finite :=
    hf.meromorphicOn.divisor_ball_support_finite
  set s := hd_fin.toFinset with hs_def
  set N := ∑ a ∈ s, (|divisor f (ball 0 ρ) a| : ℝ) with hN_def
  have hT₀ : 0 ≤ T := characteristic_nonneg (by linarith)
  have hA₀ : 0 ≤ A := circleAverage_nonneg_of_nonneg fun z _ ↦ abs_nonneg _
  have hK₀ : 0 ≤ K := mul_nonneg (by positivity) hA₀
  have hβ₀ : 0 ≤ β := inv_nonneg.2 hρr₀.le
  have hN₀ : 0 ≤ N := Finset.sum_nonneg fun a _ ↦ abs_nonneg _
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hN_finsum : ∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ) = N := by
    rw [hN_def]
    refine finsum_eq_sum_of_support_subset _ fun a ha ↦ ?_
    rw [hs_def, Finite.coe_toFinset]
    simpa only [mem_support, ne_eq, abs_eq_zero, Int.cast_eq_zero] using ha
  -- Step 1: the pointwise bound on the circle `|w| = r` (differentiated Poisson–Jensen formula),
  -- regrouped as a constant plus a sum of simple poles
  have step1 : ∀ᶠ w in codiscreteWithin (sphere (0 : ℂ) r),
      ‖logDeriv f w‖ ≤ (K + N * β) + ∑ a ∈ s, (|divisor f (ball 0 ρ) a| : ℝ) * ‖w - a‖⁻¹ := by
    filter_upwards [(hf.meromorphicOn (s := closedBall 0 ρ)).eventually_norm_logDeriv_le
      (fun u _ ↦ hdeg u) hrρ] with w hw
    have hsupp : support (fun a ↦ (|divisor f (ball 0 ρ) a| : ℝ) * (‖w - a‖⁻¹ + (ρ - r)⁻¹))
        ⊆ ↑s := fun a ha ↦ by
      rw [hs_def, Finite.coe_toFinset]
      exact mem_support.2 fun h₀ ↦ (mem_support.1 ha) (by simp [h₀])
    rw [finsum_eq_sum_of_support_subset _ hsupp] at hw
    calc ‖logDeriv f w‖
        ≤ K + ∑ a ∈ s, (|divisor f (ball 0 ρ) a| : ℝ) * (‖w - a‖⁻¹ + β) := hw
      _ = (K + N * β) + ∑ a ∈ s, (|divisor f (ball 0 ρ) a| : ℝ) * ‖w - a‖⁻¹ := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hN_def]
          ring
  -- Step 2: the exponent-`1/2` trick
  have step2 : proximity (logDeriv f) ⊤ r
      ≤ log⁺ (K + N * β) + 2 * log⁺ N + log⁺ r⁻¹ + 8 * Real.log 2 := by
    rw [proximity_top]
    exact circleAverage_posLog_norm_le_of_le_add_sum_inv_norm_sub hr₀
      (add_nonneg hK₀ (mul_nonneg hN₀ hβ₀))
      (fun a ha ↦ by exact_mod_cast Int.one_le_abs (mem_support.1 (hd_fin.mem_toFinset.1 ha)))
      hf.logDeriv.meromorphicOn.circleIntegrable_posLog_norm step1
  -- Step 3: the kernel constant and the divisor mass are controlled by `characteristic f ⊤ R`
  have hA_le : A ≤ 2 * T + c_f := circleAverage_abs_log_norm_le hf h1ρ hρR.le
  have hN_le : N ≤ (2 * T + c_f) * (2 * R * (R - r)⁻¹) := by
    have h₁ : N * ((R - r) / 2) ≤ R * (2 * T + c_f) := by
      have h₂ := finsum_abs_divisor_le hf h1ρ hρR
      rwa [hN_finsum, hR_ρ] at h₂
    calc N ≤ R * (2 * T + c_f) / ((R - r) / 2) := (le_div_iff₀ (by positivity)).2 h₁
      _ = (2 * T + c_f) * (2 * R * (R - r)⁻¹) := by
          rw [div_div_eq_mul_div, div_eq_mul_inv]
          ring
  -- Step 4: `log⁺` of the kernel constant and of the divisor mass
  have two_mul_le : ∀ x : ℝ, log⁺ (2 * x) ≤ Real.log 2 + log⁺ x := fun x ↦ by
    simpa using posLog_nat_mul (n := 2) (x := x)
  have hlogA : log⁺ A ≤ 2 * Real.log 2 + log⁺ T + log⁺ c_f := by
    have h₁ : log⁺ A ≤ Real.log 2 + log⁺ (2 * T) + log⁺ c_f :=
      (posLog_le_posLog (neg_one_lt_zero.le.trans hA₀) hA_le).trans posLog_add
    linarith [two_mul_le T]
  have hlogβ : log⁺ β ≤ Real.log 2 + log⁺ (R - r)⁻¹ := by
    have h₁ : β = 2 * (R - r)⁻¹ := by rw [hβ_def, hρ_r, inv_div, div_eq_mul_inv]
    rw [h₁]
    exact two_mul_le _
  have hlogK : log⁺ K ≤ 5 * Real.log 2 + Real.log R + 2 * log⁺ (R - r)⁻¹ + log⁺ T + log⁺ c_f := by
    have h₁ : K = 2 * ρ * β ^ 2 * A := by rw [hK_def, hβ_def, div_eq_mul_inv, ← inv_pow]
    have h₂ : log⁺ (2 * ρ) ≤ Real.log 2 + Real.log R := by
      have h₃ : log⁺ ρ ≤ Real.log R :=
        (posLog_le_posLog (by linarith) hρR.le).trans_eq
          (posLog_eq_log (by rw [abs_of_pos hR₀]; linarith))
      linarith [two_mul_le ρ]
    have h₄ : log⁺ (β ^ 2) = 2 * log⁺ β := by rw [posLog_pow]; norm_num
    calc log⁺ K = log⁺ (2 * ρ * β ^ 2 * A) := by rw [h₁]
      _ ≤ log⁺ (2 * ρ * β ^ 2) + log⁺ A := posLog_mul
      _ ≤ log⁺ (2 * ρ) + log⁺ (β ^ 2) + log⁺ A := by
          linarith [posLog_mul (x := 2 * ρ) (y := β ^ 2)]
      _ ≤ 5 * Real.log 2 + Real.log R + 2 * log⁺ (R - r)⁻¹ + log⁺ T + log⁺ c_f := by
          rw [h₄]
          linarith
  have hlogN : log⁺ N ≤ 3 * Real.log 2 + Real.log R + log⁺ (R - r)⁻¹ + log⁺ T + log⁺ c_f := by
    have h₁ : log⁺ (2 * T + c_f) ≤ 2 * Real.log 2 + log⁺ T + log⁺ c_f := by
      linarith [posLog_add (x := 2 * T) (y := c_f), two_mul_le T]
    have h₂ : log⁺ (2 * R * (R - r)⁻¹) ≤ Real.log 2 + Real.log R + log⁺ (R - r)⁻¹ := by
      have h₃ : log⁺ (2 * R) ≤ Real.log 2 + Real.log R := by
        simpa only [posLog_eq_log (x := R) (by rw [abs_of_pos hR₀]; linarith)] using two_mul_le R
      linarith [posLog_mul (x := 2 * R) (y := (R - r)⁻¹)]
    calc log⁺ N ≤ log⁺ ((2 * T + c_f) * (2 * R * (R - r)⁻¹)) :=
          posLog_le_posLog (neg_one_lt_zero.le.trans hN₀) hN_le
      _ ≤ log⁺ (2 * T + c_f) + log⁺ (2 * R * (R - r)⁻¹) := posLog_mul
      _ ≤ 3 * Real.log 2 + Real.log R + log⁺ (R - r)⁻¹ + log⁺ T + log⁺ c_f := by linarith
  -- Step 5: collect
  have hlogr : log⁺ r⁻¹ = 0 := by
    rw [posLog_eq_zero_iff, abs_of_pos (inv_pos.2 hr₀)]
    exact inv_le_one_of_one_le₀ hr
  have hlogKN : log⁺ (K + N * β) ≤ Real.log 2 + log⁺ K + log⁺ N + log⁺ β := by
    linarith [posLog_add (x := K) (y := N * β), posLog_mul (x := N) (y := β)]
  have key : proximity (logDeriv f) ⊤ r
      ≤ 4 * log⁺ T + 4 * Real.log R + 6 * log⁺ (R - r)⁻¹ + C₀ := by
    rw [hC₀_def]
    linarith
  have hprod : 0 ≤ C₀ * (log⁺ T + Real.log R + log⁺ (R - r)⁻¹) := by
    apply mul_nonneg hC₀
    linarith [posLog_nonneg (x := T), posLog_nonneg (x := (R - r)⁻¹)]
  calc proximity (logDeriv f) ⊤ r
      ≤ 4 * log⁺ T + 4 * Real.log R + 6 * log⁺ (R - r)⁻¹ + C₀ := key
    _ ≤ (6 + C₀) * (log⁺ T + Real.log R + log⁺ (R - r)⁻¹ + 1) := by
        have h₁ := posLog_nonneg (x := T)
        have h₂ := posLog_nonneg (x := (R - r)⁻¹)
        nlinarith [hprod]
