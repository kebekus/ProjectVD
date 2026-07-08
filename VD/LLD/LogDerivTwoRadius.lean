/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.Cartan
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import VD.LLD.CircleAverageEstimates
import VD.LLD.CountingEstimate
import VD.LLD.PoissonJensenDeriv
import VD.LLD.PosLog
import VD.MathlibPending.CharacteristicMoebius

/-!
# The Two-Radius Estimate — LLD work package C4 (theorem T1)

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §5.

Mathlib target: `Mathlib/Analysis/Complex/ValueDistribution/LogDerivLemma.lean` (part 1).
Dependencies: `MeromorphicLogDeriv.lean`, `PoissonJensenDeriv.lean`,
`CircleAverageEstimates.lean`, `CountingEstimate.lean`.

This file proves the **two-radius estimate** for the Lemma on the Logarithmic Derivative,
`ValueDistribution.exists_proximity_logDeriv_le`: for every meromorphic function `f` on the
complex plane there exists a constant `c` such that for all radii `1 ≤ r < R`,

```
proximity (logDeriv f) ⊤ r ≤ c * (log⁺ (characteristic f ⊤ R) + log R + log⁺ (R - r)⁻¹ + 1).
```

The statement is fully exceptional-set-free; it is the analytic core of the Lemma on the
Logarithmic Derivative. The proof runs along the classical Nevanlinna route, with the
intermediate radius `ρ := (r + R) / 2`:

1. The differentiated Poisson–Jensen formula (B6) gives, away from a discrete subset of the
   circle `|w| = r`, the pointwise bound
   `‖logDeriv f w‖ ≤ K + ∑ |D a| * (‖w - a‖⁻¹ + (ρ - r)⁻¹)`, where `K` is a kernel constant
   controlled by the circle average of `|log ‖f ·‖|` at radius `ρ`, and `D` is the divisor of
   `f` on `ball 0 ρ`.
2. The **exponent-1/2 trick**: taking square roots turns the singular sum into one whose
   circle average is bounded *uniformly* in the base points (C2).
3. Jensen's inequality for circle averages of `log⁺` (C1), applied to the explicit bound
   function, never to `‖logDeriv f‖ ^ (1/2)` itself.
4. The kernel constant is bounded by `2 * characteristic f ⊤ R + O_f(1)` using the First Main
   Theorem, and the number of zeros and poles by the counting estimate (C3).

The degenerate case where `f` vanishes away from a discrete set is handled separately: there,
`logDeriv f` vanishes away from a discrete set and the proximity function is zero.
-/

open Complex Filter Function MeromorphicOn Metric Real Set Topology ValueDistribution

/-!
## Elementary Helper Lemmas
-/

/-- The square root is subadditive. -/
private lemma sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  have h : x + y ≤ (√x + √y) ^ 2 := by
    rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
    nlinarith [mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc √(x + y)
      ≤ √((√x + √y) ^ 2) := Real.sqrt_le_sqrt h
    _ = √x + √y := Real.sqrt_sq (by positivity)

/-- The square root of a sum of nonnegative terms is at most the sum of the square roots. -/
private lemma sqrt_sum_le {ι : Type*} {s : Finset ι} {φ : ι → ℝ} (hφ : ∀ i ∈ s, 0 ≤ φ i) :
    √(∑ i ∈ s, φ i) ≤ ∑ i ∈ s, √(φ i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc √(φ a + ∑ i ∈ t, φ i)
        ≤ √(φ a) + √(∑ i ∈ t, φ i) :=
          sqrt_add_le (hφ a (Finset.mem_insert_self a t))
            (Finset.sum_nonneg fun i hi ↦ hφ i (Finset.mem_insert_of_mem hi))
      _ ≤ √(φ a) + ∑ i ∈ t, √(φ i) :=
          add_le_add le_rfl (ih fun i hi ↦ hφ i (Finset.mem_insert_of_mem hi))

/-- Conversion between the square root of an inverse and a real power. -/
private lemma sqrt_inv_eq_rpow {x : ℝ} (hx : 0 ≤ x) : √x⁻¹ = x ^ (-(2:ℝ)⁻¹) := by
  rw [Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg hx]
  norm_num

/-- The positive part of the logarithm is dominated by the absolute value. -/
private lemma posLog_le_abs (x : ℝ) : log⁺ x ≤ |x| := by
  rcases le_or_gt |x| 1 with h | h
  · rw [(posLog_eq_zero_iff x).2 h]
    exact abs_nonneg x
  · rw [← posLog_abs, posLog_eq_log (by rw [abs_abs]; exact h.le)]
    linarith [Real.log_le_sub_one_of_pos (lt_trans one_pos h : (0:ℝ) < |x|)]

/-- The norm of a circle average is at most the circle average of the norms. -/
private lemma norm_circleAverage_le (F : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    ‖circleAverage F c R‖ ≤ circleAverage (fun z ↦ ‖F z‖) c R := by
  rw [circleAverage_def, circleAverage_def, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 2 * π), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm (by positivity)) (by positivity)

/-- Circle averages respect the `≤` relation between functions that holds away from a discrete
set. -/
private lemma circleAverage_mono_codiscreteWithin {f₁ f₂ : ℂ → ℝ} {R : ℝ} (hR : R ≠ 0)
    (hf₁ : CircleIntegrable f₁ 0 R) (hf₂ : CircleIntegrable f₂ 0 R)
    (h : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |R|), f₁ z ≤ f₂ z) :
    circleAverage f₁ 0 R ≤ circleAverage f₂ 0 R := by
  rw [circleAverage_def, circleAverage_def, smul_eq_mul, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_ae_restrict (by positivity) hf₁ hf₂
  apply ae_restrict_le_codiscreteWithin measurableSet_Icc
  apply codiscreteWithin_mono (Set.subset_univ _)
  exact circleMap_preimage_codiscrete hR h

/-- The derived Herglotz–Riesz kernel `ζ ↦ 2ζ/(ζ-w)²` is continuous on the circle
`sphere 0 |R|` whenever `w ∈ ball 0 R`. -/
private lemma continuousOn_derivedKernel {w : ℂ} {R : ℝ} (hw : w ∈ ball 0 R) :
    ContinuousOn (fun ζ : ℂ ↦ 2 * ζ / (ζ - w) ^ 2) (sphere (0 : ℂ) |R|) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro z hz
  apply pow_ne_zero
  rw [sub_ne_zero]
  rintro rfl
  rw [mem_sphere_zero_iff_norm] at hz
  rw [mem_ball_zero_iff, hz] at hw
  exact absurd hw (not_lt.2 (le_abs_self R))

/-!
## Step 1–4: The Analytic Estimate

For fixed radii `1 ≤ r < ρ`, the proximity function of `logDeriv f` at radius `r` is bounded
by `log⁺` of an explicit expression involving the circle average of `|log ‖f ·‖|` at radius
`ρ` and the total mass of the divisor of `f` on `ball 0 ρ`.
-/

private lemma proximity_logDeriv_le {f : ℂ → ℂ} {r ρ : ℝ} (hf : Meromorphic f)
    (h'f : ∀ u, meromorphicOrderAt f u ≠ ⊤) (hr : 1 ≤ r) (hrρ : r < ρ) :
    proximity (logDeriv f) ⊤ r
      ≤ 2 * log⁺ (√(2 * ρ / (ρ - r) ^ 2 * circleAverage (fun ζ ↦ |Real.log ‖f ζ‖|) 0 ρ)
            + (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) * (4 + (ρ - r) ^ (-(2:ℝ)⁻¹)))
          + 2 * Real.log 2 := by
  have hr₀ : (0:ℝ) < r := by linarith
  have hρ₀ : (0:ℝ) < ρ := by linarith
  have hρr : (0:ℝ) < ρ - r := by linarith
  -- Abbreviations: the kernel constant `K` and the divisor mass
  set A := circleAverage (fun ζ ↦ |Real.log ‖f ζ‖|) 0 ρ with hA_def
  set K := 2 * ρ / (ρ - r) ^ 2 * A with hK_def
  have hd_fin : (divisor f (ball 0 ρ)).support.Finite :=
    hf.meromorphicOn.divisor_ball_support_finite
  set s := hd_fin.toFinset with hs_def
  have hA₀ : 0 ≤ A := circleAverage_nonneg_of_nonneg fun z _ ↦ abs_nonneg _
  have hK₀ : 0 ≤ K := mul_nonneg (by positivity) hA₀
  have hcoeff : ∀ a : ℂ, (0:ℝ) ≤ (|divisor f (ball 0 ρ) a| : ℝ) :=
    fun a ↦ abs_nonneg _
  -- The explicit bound function
  set g : ℂ → ℝ := fun w ↦ √K + ∑ a ∈ s,
      (|divisor f (ball 0 ρ) a| : ℝ) * (‖w - a‖ ^ (-(2:ℝ)⁻¹) + (ρ - r) ^ (-(2:ℝ)⁻¹))
    with hg_def
  have hg₀ : ∀ w, 0 ≤ g w := by
    intro w
    apply add_nonneg (Real.sqrt_nonneg _)
    apply Finset.sum_nonneg fun a _ ↦ mul_nonneg (hcoeff a) ?_
    exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hρr.le _)
  -- Step 1: the pointwise bound away from a discrete subset of the circle `|w| = r`, from the
  -- differentiated Poisson–Jensen formula (B6) and the canonical-factor bound (B5).
  have step1 : ∀ᶠ w in codiscreteWithin (sphere (0 : ℂ) r),
      ‖logDeriv f w‖
        ≤ K + ∑ a ∈ s, (|divisor f (ball 0 ρ) a| : ℝ) * (‖w - a‖⁻¹ + (ρ - r)⁻¹) := by
    have hB6 := (hf.meromorphicOn (s := closedBall 0 ρ)).logDeriv_eqOn_codiscrete
      (fun u ↦ h'f u)
    have hsub : sphere (0 : ℂ) r ⊆ ball 0 ρ := fun z hz ↦ by
      rw [mem_sphere_zero_iff_norm] at hz
      rw [mem_ball_zero_iff, hz]
      exact hrρ
    filter_upwards [hB6.filter_mono (codiscreteWithin_mono hsub),
      self_mem_codiscreteWithin (sphere (0:ℂ) r)] with w hw₁ hw₂
    rw [mem_sphere_zero_iff_norm] at hw₂
    have hwball : w ∈ ball (0:ℂ) ρ := by rw [mem_ball_zero_iff, hw₂]; exact hrρ
    rw [hw₁]
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
    -- The kernel term is bounded by `K`
    · refine le_trans (norm_circleAverage_le _ _ _) ?_
      have hlog_int : CircleIntegrable (fun ζ ↦ |Real.log ‖f ζ‖|) 0 ρ :=
        hf.meromorphicOn.circleIntegrable_log_norm.abs
      have hint₁ : CircleIntegrable
          (fun ζ ↦ ‖(2 * ζ / (ζ - w) ^ 2) • (Real.log ‖f ζ‖ : ℂ)‖) 0 ρ := by
        have h₁ := hlog_int.smul_of_continuousOn (continuousOn_derivedKernel hwball).norm
        have h₂ : (fun ζ : ℂ ↦ ‖2 * ζ / (ζ - w) ^ 2‖) • (fun ζ ↦ |Real.log ‖f ζ‖|)
            = fun ζ ↦ ‖(2 * ζ / (ζ - w) ^ 2) • (Real.log ‖f ζ‖ : ℂ)‖ := by
          funext ζ
          simp
        rwa [h₂] at h₁
      have hint₂ : CircleIntegrable (fun ζ ↦ 2 * ρ / (ρ - r) ^ 2 * |Real.log ‖f ζ‖|) 0 ρ :=
        hlog_int.const_smul (a := 2 * ρ / (ρ - r) ^ 2)
      refine le_trans (circleAverage_mono hint₁ hint₂ ?_) ?_
      · intro ζ hζ
        rw [mem_sphere_zero_iff_norm, abs_of_pos hρ₀] at hζ
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        have h₁ : ρ - r ≤ ‖ζ - w‖ := by
          have h₂ := norm_sub_norm_le ζ w
          rw [hζ, hw₂] at h₂
          linarith
        rw [norm_div, norm_mul, norm_pow, hζ]
        have h₃ : ‖(2:ℂ)‖ = 2 := by norm_num
        rw [h₃]
        gcongr
      · have h₁ : (fun ζ ↦ 2 * ρ / (ρ - r) ^ 2 * |Real.log ‖f ζ‖|)
            = fun ζ ↦ (2 * ρ / (ρ - r) ^ 2) • |Real.log ‖f ζ‖| := rfl
        rw [h₁, circleAverage_fun_smul, smul_eq_mul, hK_def]
    -- The divisor term is bounded by the singular sum, using B5
    · have hconv : (∑ᶠ a, (divisor f (ball 0 ρ) a) • logDeriv (canonicalFactor ρ a) w)
          = ∑ a ∈ s, (divisor f (ball 0 ρ) a) • logDeriv (canonicalFactor ρ a) w := by
        apply finsum_eq_sum_of_support_subset
        intro a ha
        rw [hs_def, Finite.coe_toFinset]
        exact mem_support.2 fun h₀ ↦ (mem_support.1 ha) (by simp [h₀])
      rw [hconv]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun a ha ↦ ?_)
      have haball : a ∈ ball (0:ℂ) ρ :=
        (divisor f (ball 0 ρ)).supportWithinDomain (hd_fin.mem_toFinset.1 ha)
      rw [← Int.cast_smul_eq_zsmul ℂ, norm_smul, Complex.norm_intCast]
      exact mul_le_mul_of_nonneg_left
        (Complex.norm_logDeriv_canonicalFactor_le (mem_ball_zero_iff.1 haball) hw₂ hrρ)
        (hcoeff a)
  -- Step 2: the square-root trick, pointwise
  have step2 : ∀ᶠ w in codiscreteWithin (sphere (0 : ℂ) r),
      log⁺ ‖logDeriv f w‖ ≤ 2 * log⁺ (g w) := by
    filter_upwards [step1] with w hw
    have hsq : √‖logDeriv f w‖ ≤ g w := by
      have hterm : ∀ a ∈ s, (0:ℝ)
          ≤ (|divisor f (ball 0 ρ) a| : ℝ) * (‖w - a‖⁻¹ + (ρ - r)⁻¹) :=
        fun a _ ↦ mul_nonneg (hcoeff a) (by positivity)
      calc √‖logDeriv f w‖
          ≤ √(K + ∑ a ∈ s, (|divisor f (ball 0 ρ) a| : ℝ) * (‖w - a‖⁻¹ + (ρ - r)⁻¹)) :=
            Real.sqrt_le_sqrt hw
        _ ≤ √K + √(∑ a ∈ s, (|divisor f (ball 0 ρ) a| : ℝ) * (‖w - a‖⁻¹ + (ρ - r)⁻¹)) :=
            sqrt_add_le hK₀ (Finset.sum_nonneg hterm)
        _ ≤ √K + ∑ a ∈ s, √((|divisor f (ball 0 ρ) a| : ℝ) * (‖w - a‖⁻¹ + (ρ - r)⁻¹)) :=
            add_le_add le_rfl (sqrt_sum_le hterm)
        _ ≤ g w := by
            change _ ≤ √K + ∑ a ∈ s,
              (|divisor f (ball 0 ρ) a| : ℝ) * (‖w - a‖ ^ (-(2:ℝ)⁻¹) + (ρ - r) ^ (-(2:ℝ)⁻¹))
            refine add_le_add le_rfl (Finset.sum_le_sum fun a ha ↦ ?_)
            have hm : (1:ℝ) ≤ (|divisor f (ball 0 ρ) a| : ℝ) := by
              exact_mod_cast Int.one_le_abs (mem_support.1 (hd_fin.mem_toFinset.1 ha))
            calc √((|divisor f (ball 0 ρ) a| : ℝ) * (‖w - a‖⁻¹ + (ρ - r)⁻¹))
                = √(|divisor f (ball 0 ρ) a| : ℝ) * √(‖w - a‖⁻¹ + (ρ - r)⁻¹) :=
                  Real.sqrt_mul (hcoeff a) _
              _ ≤ (|divisor f (ball 0 ρ) a| : ℝ) * (√(‖w - a‖⁻¹) + √((ρ - r)⁻¹)) := by
                  apply mul_le_mul (Real.sqrt_le_self_iff.2 (Or.inr hm))
                    (sqrt_add_le (by positivity) (by positivity)) (Real.sqrt_nonneg _)
                    (by linarith)
              _ = (|divisor f (ball 0 ρ) a| : ℝ)
                    * (‖w - a‖ ^ (-(2:ℝ)⁻¹) + (ρ - r) ^ (-(2:ℝ)⁻¹)) := by
                  rw [sqrt_inv_eq_rpow (norm_nonneg _), sqrt_inv_eq_rpow hρr.le]
    calc log⁺ ‖logDeriv f w‖
        = log⁺ ((√‖logDeriv f w‖) ^ 2) := by rw [Real.sq_sqrt (norm_nonneg _)]
      _ = 2 * log⁺ (√‖logDeriv f w‖) := by rw [posLog_pow]; norm_num
      _ ≤ 2 * log⁺ (g w) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact posLog_le_posLog (Real.sqrt_nonneg _) hsq
  -- Integrability of the functions involved
  have hld : Meromorphic (logDeriv f) := fun x ↦ (hf x).logDeriv
  have int_lhs : CircleIntegrable (fun w ↦ log⁺ ‖logDeriv f w‖) 0 r :=
    hld.meromorphicOn.circleIntegrable_posLog_norm
  have int_sum : CircleIntegrable (fun w ↦ ∑ a ∈ s,
      (|divisor f (ball 0 ρ) a| : ℝ) * (‖w - a‖ ^ (-(2:ℝ)⁻¹) + (ρ - r) ^ (-(2:ℝ)⁻¹))) 0 r := by
    apply CircleIntegrable.fun_sum
    intro a _
    exact ((Real.circleIntegrable_norm_sub_rpow a r).add
      (circleIntegrable_const ((ρ - r) ^ (-(2:ℝ)⁻¹)) 0 r)).const_smul
  have int_g : CircleIntegrable g 0 r := (circleIntegrable_const (√K) 0 r).add int_sum
  have int_posLog_g : CircleIntegrable (fun w ↦ log⁺ (g w)) 0 r := by
    apply IntervalIntegrable.mono_fun int_g.abs
    · exact continuous_posLog.comp_aestronglyMeasurable
        (intervalIntegrable_iff.1 int_g).aestronglyMeasurable
    · filter_upwards with θ
      simp only [Pi.abs_apply, Real.norm_eq_abs, abs_abs]
      rw [abs_of_nonneg posLog_nonneg]
      exact posLog_le_abs _
  -- Step 3: integrate the pointwise bound
  have step3 : proximity (logDeriv f) ⊤ r ≤ 2 * circleAverage (fun w ↦ log⁺ (g w)) 0 r := by
    rw [proximity_top]
    calc circleAverage (fun w ↦ log⁺ ‖logDeriv f w‖) 0 r
        ≤ circleAverage (fun w ↦ 2 * log⁺ (g w)) 0 r := by
          apply circleAverage_mono_codiscreteWithin hr₀.ne' int_lhs
            (int_posLog_g.const_smul (a := (2:ℝ)))
          rw [abs_of_pos hr₀]
          exact step2
      _ = 2 * circleAverage (fun w ↦ log⁺ (g w)) 0 r := by
          have h₁ : (fun w ↦ 2 * log⁺ (g w)) = fun w ↦ (2:ℝ) • log⁺ (g w) := rfl
          rw [h₁, circleAverage_fun_smul, smul_eq_mul]
  -- Step 4: Jensen's inequality (C1) and the uniform singular-average bound (C2)
  have step4 : circleAverage g 0 r
      ≤ √K + (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) * (4 + (ρ - r) ^ (-(2:ℝ)⁻¹)) := by
    have hN : (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) = ∑ a ∈ s, (|divisor f (ball 0 ρ) a| : ℝ) := by
      apply finsum_eq_sum_of_support_subset
      intro a ha
      rw [hs_def, Finite.coe_toFinset]
      apply mem_support.2
      intro h₀
      exact (mem_support.1 ha) (by simp [h₀])
    have e₁ : circleAverage g 0 r = √K + ∑ a ∈ s, (|divisor f (ball 0 ρ) a| : ℝ)
        * (circleAverage (‖· - a‖ ^ (-(2:ℝ)⁻¹)) 0 r + (ρ - r) ^ (-(2:ℝ)⁻¹)) := by
      rw [hg_def]
      have h₁ : (fun w ↦ √K + ∑ a ∈ s, (|divisor f (ball 0 ρ) a| : ℝ)
          * (‖w - a‖ ^ (-(2:ℝ)⁻¹) + (ρ - r) ^ (-(2:ℝ)⁻¹)))
          = (fun _ ↦ √K) + fun w ↦ ∑ a ∈ s, (|divisor f (ball 0 ρ) a| : ℝ)
            * (‖w - a‖ ^ (-(2:ℝ)⁻¹) + (ρ - r) ^ (-(2:ℝ)⁻¹)) := rfl
      rw [h₁, circleAverage_add (circleIntegrable_const (√K) 0 r) int_sum, circleAverage_const]
      congr 1
      have h_each : ∀ a ∈ s, CircleIntegrable (fun w ↦ (|divisor f (ball 0 ρ) a| : ℝ)
          * (‖w - a‖ ^ (-(2:ℝ)⁻¹) + (ρ - r) ^ (-(2:ℝ)⁻¹))) 0 r :=
        fun a _ ↦ ((Real.circleIntegrable_norm_sub_rpow a r).add
          (circleIntegrable_const ((ρ - r) ^ (-(2:ℝ)⁻¹)) 0 r)).const_smul
      rw [circleAverage_fun_sum h_each]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      have h₂ : (fun w ↦ (|divisor f (ball 0 ρ) a| : ℝ)
          * (‖w - a‖ ^ (-(2:ℝ)⁻¹) + (ρ - r) ^ (-(2:ℝ)⁻¹)))
          = fun w ↦ (|divisor f (ball 0 ρ) a| : ℝ)
            • (‖w - a‖ ^ (-(2:ℝ)⁻¹) + (ρ - r) ^ (-(2:ℝ)⁻¹)) := rfl
      rw [h₂, circleAverage_fun_smul, smul_eq_mul]
      congr 1
      have h₃ : (fun w : ℂ ↦ ‖w - a‖ ^ (-(2:ℝ)⁻¹) + (ρ - r) ^ (-(2:ℝ)⁻¹))
          = (‖· - a‖ ^ (-(2:ℝ)⁻¹)) + fun _ ↦ (ρ - r) ^ (-(2:ℝ)⁻¹) := rfl
      rw [h₃, circleAverage_add (Real.circleIntegrable_norm_sub_rpow a r)
        (circleIntegrable_const _ 0 r), circleAverage_const]
    rw [e₁, hN]
    refine add_le_add le_rfl ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left ?_ (hcoeff a)
    refine add_le_add ?_ le_rfl
    calc circleAverage (‖· - a‖ ^ (-(2:ℝ)⁻¹)) 0 r
        ≤ 4 * r ^ (-(2:ℝ)⁻¹) := Real.circleAverage_norm_sub_rpow_le hr₀
      _ ≤ 4 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.rpow_le_one_of_one_le_of_nonpos hr (by norm_num)
      _ = 4 := mul_one 4
  -- Conclusion via C1
  have hC1 : circleAverage (fun w ↦ log⁺ (g w)) 0 r
      ≤ log⁺ (circleAverage g 0 r) + Real.log 2 :=
    Real.circleAverage_posLog_le_posLog_circleAverage (fun z _ ↦ hg₀ z) int_g
  have havg₀ : 0 ≤ circleAverage g 0 r := circleAverage_nonneg_of_nonneg fun z _ ↦ hg₀ z
  have hmono := posLog_le_posLog havg₀ step4
  calc proximity (logDeriv f) ⊤ r
      ≤ 2 * circleAverage (fun w ↦ log⁺ (g w)) 0 r := step3
    _ ≤ 2 * (log⁺ (circleAverage g 0 r) + Real.log 2) := by linarith
    _ ≤ 2 * (log⁺ (√K + (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ))
          * (4 + (ρ - r) ^ (-(2:ℝ)⁻¹))) + Real.log 2) := by linarith
    _ = 2 * log⁺ (√K + (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ))
          * (4 + (ρ - r) ^ (-(2:ℝ)⁻¹))) + 2 * Real.log 2 := by ring

/-!
## Step 5: Bounding the Kernel Constant

The circle average of `|log ‖f ·‖|` at radius `ρ` is bounded by the characteristic function at
any radius `R ≥ ρ`, using the First Main Theorem and monotonicity of the characteristic.
-/

private lemma circleAverage_abs_log_norm_le {f : ℂ → ℂ} {ρ R : ℝ} (hf : Meromorphic f)
    (hρ : 1 ≤ ρ) (hρR : ρ ≤ R) :
    circleAverage (fun ζ ↦ |Real.log ‖f ζ‖|) 0 ρ
      ≤ 2 * characteristic f ⊤ R
        + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have hρ₀ : (0:ℝ) < ρ := by linarith
  -- Split `|log|` into the two proximity functions
  have e₁ : circleAverage (fun ζ ↦ |Real.log ‖f ζ‖|) 0 ρ
      = proximity f ⊤ ρ + proximity f⁻¹ ⊤ ρ := by
    rw [proximity_top, proximity_top]
    have h₁ : (fun ζ ↦ |Real.log ‖f ζ‖|)
        = fun ζ ↦ log⁺ ‖f ζ‖ + log⁺ ‖f⁻¹ ζ‖ := by
      funext ζ
      rw [Pi.inv_apply, norm_inv]
      exact Real.abs_log_eq_posLog_add_posLog_inv _
    rw [h₁]
    exact circleAverage_fun_add hf.meromorphicOn.circleIntegrable_posLog_norm
      hf.inv.meromorphicOn.circleIntegrable_posLog_norm
  rw [e₁]
  -- Compare with the characteristic functions, via the First Main Theorem
  have h₁ : proximity f ⊤ ρ ≤ characteristic f ⊤ ρ :=
    le_add_of_nonneg_right (logCounting_nonneg hρ)
  have h₂ : proximity f⁻¹ ⊤ ρ ≤ characteristic f⁻¹ ⊤ ρ :=
    le_add_of_nonneg_right (logCounting_nonneg hρ)
  have h₃ := abs_le.1 (characteristic_sub_characteristic_inv_le hf (R := ρ))
  have h₄ : characteristic f ⊤ ρ ≤ characteristic f ⊤ R :=
    characteristic_monotoneOn hf (mem_Ioi.2 hρ₀) (mem_Ioi.2 (by linarith)) hρR
  linarith [h₃.1]

/-!
## Step 6: Bounding the Divisor Mass

The total mass of the divisor of `f` on `ball 0 ρ`, weighted by `log (R / ρ)`, is bounded by
the characteristic function at radius `R`, using the counting estimate (C3) and the First Main
Theorem.
-/

private lemma finsum_abs_divisor_le {f : ℂ → ℂ} {ρ R : ℝ} (hf : Meromorphic f)
    (hρ : 1 ≤ ρ) (hρR : ρ < R) :
    (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) * Real.log (R / ρ)
      ≤ 2 * characteristic f ⊤ R
        + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
  classical
  have hρ₀ : (0:ℝ) < ρ := by linarith
  have habs : |ρ| = ρ := abs_of_pos hρ₀
  -- The comparison divisor: positive plus negative part of the divisor on the plane
  set D := divisor f univ with hD_def
  set E := D⁺ + D⁻ with hE_def
  have hE₀ : 0 ≤ E := add_nonneg (posPart_nonneg D) (negPart_nonneg D)
  have hE₀' : ∀ z, 0 ≤ E z := by
    intro z
    simpa using (Function.locallyFinsuppWithin.le_def.1 hE₀) z
  -- Finiteness of the supports involved
  have hd_fin : (divisor f (ball 0 ρ)).support.Finite :=
    hf.meromorphicOn.divisor_ball_support_finite
  have hE_fin : ((E.toClosedBall ρ).support).Finite :=
    Function.locallyFinsuppWithin.finiteSupport _ (isCompact_closedBall 0 |ρ|)
  set t : Finset ℂ := hd_fin.toFinset ∪ hE_fin.toFinset with ht_def
  -- Term-wise comparison of the mass functions
  have key : ∀ a : ℂ, (|divisor f (ball 0 ρ) a| : ℝ) ≤ (E.toClosedBall ρ a : ℝ) := by
    intro a
    by_cases hab : a ∈ ball (0:ℂ) ρ
    · have h₁ : divisor f (ball 0 ρ) a = D a := by
        rw [(hf.meromorphicOn.mono_set (Set.subset_univ _)).divisor_apply hab,
          hD_def, hf.meromorphicOn.divisor_apply (Set.mem_univ a)]
      have h₂ : E.toClosedBall ρ a = |D a| := by
        rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _
          (by rw [habs]; exact ball_subset_closedBall hab)]
        simp only [hE_def, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
          Function.locallyFinsuppWithin.posPart_apply,
          Function.locallyFinsuppWithin.negPart_apply]
        exact posPart_add_negPart (D a)
      rw [h₁, h₂]
      exact Int.cast_abs.symm.le
    · have h₁ : divisor f (ball 0 ρ) a = 0 := by
        by_contra hne
        exact hab ((divisor f (ball 0 ρ)).supportWithinDomain (mem_support.2 hne))
      rw [h₁]
      simp only [abs_zero, Int.cast_zero]
      by_cases haE : a ∈ closedBall (0:ℂ) |ρ|
      · rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ haE]
        exact_mod_cast hE₀' a
      · rw [show E.toClosedBall ρ a = 0 by
          by_contra hne
          exact haE (Function.locallyFinsuppWithin.toClosedBall_support_subset_closedBall E
            (mem_support.2 hne))]
        simp
  -- Compare the two finite sums
  have hsum : (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) ≤ ∑ᶠ z, (E.toClosedBall ρ z : ℝ) := by
    have h₁ : (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) = ∑ a ∈ t, (|divisor f (ball 0 ρ) a| : ℝ) := by
      apply finsum_eq_sum_of_support_subset
      intro a ha
      simp only [mem_support, ne_eq, Int.cast_eq_zero, abs_eq_zero] at ha
      exact Finset.mem_union_left _ (hd_fin.mem_toFinset.2 (mem_support.2 ha))
    have h₂ : (∑ᶠ z, (E.toClosedBall ρ z : ℝ)) = ∑ z ∈ t, (E.toClosedBall ρ z : ℝ) := by
      apply finsum_eq_sum_of_support_subset
      intro z hz
      simp only [mem_support, ne_eq, Int.cast_eq_zero] at hz
      exact Finset.mem_union_right _ (hE_fin.mem_toFinset.2 (mem_support.2 hz))
    rw [h₁, h₂]
    exact Finset.sum_le_sum fun a _ ↦ key a
  -- Apply the counting estimate (C3)
  have hC3 := Function.locallyFinsuppWithin.sum_toClosedBall_le_logCounting hE₀ hρ hρR
  -- Split the logarithmic counting function of `E` and compare with the characteristic
  have hsplit : Function.locallyFinsuppWithin.logCounting E R
      = ValueDistribution.logCounting f 0 R + ValueDistribution.logCounting f ⊤ R := by
    rw [hE_def, map_add, logCounting_zero, logCounting_top]
    rfl
  have h₅ : ValueDistribution.logCounting f ⊤ R ≤ characteristic f ⊤ R :=
    le_add_of_nonneg_left (proximity_nonneg R)
  have h₆ : ValueDistribution.logCounting f 0 R ≤ characteristic f ⊤ R
      + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
    rw [← logCounting_inv]
    have h₇ : ValueDistribution.logCounting f⁻¹ ⊤ R ≤ characteristic f⁻¹ ⊤ R :=
      le_add_of_nonneg_left (proximity_nonneg R)
    have h₈ := abs_le.1 (characteristic_sub_characteristic_inv_le hf (R := R))
    linarith [h₈.1]
  have hlog₀ : 0 ≤ Real.log (R / ρ) :=
    Real.log_nonneg ((one_le_div₀ hρ₀).2 hρR.le)
  calc (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) * Real.log (R / ρ)
      ≤ (∑ᶠ z, (E.toClosedBall ρ z : ℝ)) * Real.log (R / ρ) :=
        mul_le_mul_of_nonneg_right hsum hlog₀
    _ ≤ Function.locallyFinsuppWithin.logCounting E R := hC3
    _ ≤ 2 * characteristic f ⊤ R
        + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
        rw [hsplit]
        linarith

/-!
## The Two-Radius Estimate (Theorem T1)
-/

/-- **Two-radius estimate** for the Lemma on the Logarithmic Derivative, fully
exceptional-set-free: for a meromorphic function `f` on the complex plane, there is a constant
`c` such that for all radii `1 ≤ r < R`, the proximity function of `logDeriv f` at radius `r`
is bounded by `c * (log⁺ (characteristic f ⊤ R) + log R + log⁺ (R - r)⁻¹ + 1)`. -/
theorem ValueDistribution.exists_proximity_logDeriv_le {f : ℂ → ℂ} (hf : Meromorphic f) :
    ∃ c, ∀ r R : ℝ, 1 ≤ r → r < R →
      proximity (logDeriv f) ⊤ r
        ≤ c * (log⁺ (characteristic f ⊤ R) + Real.log R + log⁺ (R - r)⁻¹ + 1) := by
  -- Degenerate case: `f` vanishes away from a discrete set; then `logDeriv f` does, too, and
  -- the proximity function vanishes.
  by_cases hdeg : ∃ u, meromorphicOrderAt f u = ⊤
  · refine ⟨1, fun r R hr hrR ↦ ?_⟩
    have h₁ : logDeriv f =ᶠ[codiscrete ℂ] logDeriv (0 : ℂ → ℂ) :=
      logDeriv_congr_codiscreteWithin isOpen_univ
        (hf.exists_meromorphicOrderAt_eq_top_iff_eventually_zero.1 hdeg)
    have h₂ : logDeriv f =ᶠ[codiscrete ℂ] (0 : ℂ → ℂ) := by
      apply h₁.trans
      apply EventuallyEq.of_eq
      have : logDeriv (0 : ℂ → ℂ) = logDeriv (fun _ ↦ (0:ℂ)) := rfl
      rw [this, logDeriv_const]
    rw [proximity_congr_codiscrete h₂ (by linarith : r ≠ 0)]
    have h₃ : proximity (0 : ℂ → ℂ) ⊤ r = 0 := by
      rw [proximity_top]
      have : (fun x ↦ log⁺ ‖(0 : ℂ → ℂ) x‖) = fun _ ↦ (0:ℝ) := by
        funext x
        simp [posLog]
      rw [this, circleAverage_const]
    rw [h₃, one_mul]
    have := posLog_nonneg (x := characteristic f ⊤ R)
    have := posLog_nonneg (x := (R - r)⁻¹)
    have := Real.log_nonneg (by linarith : 1 ≤ R)
    linarith
  -- Main case
  push Not at hdeg
  set c_f := max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| with hc_f_def
  have hc_f₀ : 0 ≤ c_f := le_trans (abs_nonneg _) (le_max_left _ _)
  set C₀ : ℝ := 22 * Real.log 2 + 3 * log⁺ c_f with hC₀_def
  have hC₀ : 0 ≤ C₀ := by
    have h₁ : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h₂ := posLog_nonneg (x := c_f)
    linarith
  refine ⟨5 + C₀, fun r R hr hrR ↦ ?_⟩
  -- Set up the radii
  set ρ := (r + R) / 2 with hρ_def
  have hrρ : r < ρ := by rw [hρ_def]; linarith
  have hρR : ρ < R := by rw [hρ_def]; linarith
  have h1ρ : 1 ≤ ρ := by linarith
  have hρ₀ : (0:ℝ) < ρ := by linarith
  have hR₀ : (0:ℝ) < R := by linarith
  have hρr₀ : (0:ℝ) < ρ - r := by linarith
  have hRr₀ : (0:ℝ) < R - r := by linarith
  have hρ_r : ρ - r = (R - r) / 2 := by rw [hρ_def]; ring
  have hR_ρ : R - ρ = (R - r) / 2 := by rw [hρ_def]; ring
  -- Abbreviations
  set T := characteristic f ⊤ R with hT_def
  set A := circleAverage (fun ζ ↦ |Real.log ‖f ζ‖|) 0 ρ with hA_def
  set K := 2 * ρ / (ρ - r) ^ 2 * A with hK_def
  set N := ∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ) with hN_def
  have hT₀ : 0 ≤ T := characteristic_nonneg (by linarith)
  have hA₀ : 0 ≤ A := circleAverage_nonneg_of_nonneg fun z _ ↦ abs_nonneg _
  have hK₀ : 0 ≤ K := mul_nonneg (by positivity) hA₀
  have hN₀ : 0 ≤ N := by
    rw [hN_def]
    exact finsum_nonneg fun a ↦ abs_nonneg _
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hL₀ := posLog_nonneg (x := (R - r)⁻¹)
  -- The analytic estimate (steps 1–4)
  have main := proximity_logDeriv_le hf hdeg hr hrρ
  rw [← hA_def, ← hK_def, ← hN_def] at main
  -- Bound the kernel constant (step 5)
  have hA_le : A ≤ 2 * T + c_f := circleAverage_abs_log_norm_le hf h1ρ hρR.le
  -- Bound the divisor mass (step 6)
  have hN_le : N * Real.log (R / ρ) ≤ 2 * T + c_f := finsum_abs_divisor_le hf h1ρ hρR
  -- Elementary facts about `log⁺` of the inverse distances
  have hinv : (ρ - r)⁻¹ = 2 * (R - r)⁻¹ := by
    rw [hρ_r]
    field_simp
  have hpos_inv : log⁺ ((ρ - r)⁻¹) ≤ Real.log 2 + log⁺ (R - r)⁻¹ := by
    calc log⁺ ((ρ - r)⁻¹) = log⁺ (2 * (R - r)⁻¹) := by rw [hinv]
      _ ≤ log⁺ 2 + log⁺ (R - r)⁻¹ := posLog_mul
      _ = Real.log 2 + log⁺ (R - r)⁻¹ := by rw [posLog_eq_log (by norm_num)]
  -- Bound `log⁺ K`
  have hlogK : log⁺ K ≤ 5 * Real.log 2 + Real.log R + 2 * log⁺ (R - r)⁻¹
      + log⁺ T + log⁺ c_f := by
    have h₁ : log⁺ K ≤ log⁺ (2 * ρ / (ρ - r) ^ 2) + log⁺ A := posLog_mul
    have h₂ : log⁺ (2 * ρ / (ρ - r) ^ 2) ≤ Real.log 2 + Real.log R
        + 2 * (Real.log 2 + log⁺ (R - r)⁻¹) := by
      have e₁ : 2 * ρ / (ρ - r) ^ 2 = 2 * ρ * ((ρ - r)⁻¹) ^ 2 := by
        rw [div_eq_mul_inv, inv_pow]
      have h₃ : log⁺ (2 * ρ * ((ρ - r)⁻¹) ^ 2) ≤ log⁺ (2 * ρ) + log⁺ (((ρ - r)⁻¹) ^ 2) :=
        posLog_mul
      have h₄ : log⁺ (2 * ρ) ≤ Real.log 2 + Real.log R := by
        calc log⁺ (2 * ρ) ≤ log⁺ 2 + log⁺ ρ := posLog_mul
          _ ≤ Real.log 2 + Real.log R := by
              rw [posLog_eq_log (by norm_num)]
              refine add_le_add le_rfl ?_
              calc log⁺ ρ ≤ log⁺ R := posLog_le_posLog hρ₀.le (by linarith)
                _ = Real.log R := posLog_eq_log (by rw [abs_of_pos hR₀]; linarith)
      have h₅ : log⁺ (((ρ - r)⁻¹) ^ 2) = 2 * log⁺ ((ρ - r)⁻¹) := by
        rw [posLog_pow]
        norm_num
      rw [e₁]
      calc log⁺ (2 * ρ * ((ρ - r)⁻¹) ^ 2)
          ≤ log⁺ (2 * ρ) + log⁺ (((ρ - r)⁻¹) ^ 2) := h₃
        _ ≤ Real.log 2 + Real.log R + 2 * log⁺ ((ρ - r)⁻¹) := by rw [h₅]; linarith
        _ ≤ Real.log 2 + Real.log R + 2 * (Real.log 2 + log⁺ (R - r)⁻¹) := by
            linarith [hpos_inv]
    have h₆ : log⁺ A ≤ 2 * Real.log 2 + log⁺ T + log⁺ c_f := by
      calc log⁺ A ≤ log⁺ (2 * T + c_f) := posLog_le_posLog hA₀ hA_le
        _ ≤ Real.log 2 + log⁺ (2 * T) + log⁺ c_f := posLog_add
        _ ≤ Real.log 2 + (log⁺ 2 + log⁺ T) + log⁺ c_f := by
            linarith [posLog_mul (x := (2:ℝ)) (y := T)]
        _ = 2 * Real.log 2 + log⁺ T + log⁺ c_f := by
            rw [posLog_eq_log (by norm_num)]
            ring
    linarith
  -- Bound `log⁺ N`
  have hlogN : log⁺ N ≤ 3 * Real.log 2 + log⁺ T + log⁺ c_f + Real.log R
      + log⁺ (R - r)⁻¹ := by
    have hM₀ : (0:ℝ) ≤ 2 * T + c_f := by linarith
    have hlog_lb : (R - r) / (2 * R) ≤ Real.log (R / ρ) := by
      have h₁ := Real.sub_div_le_log_div hρ₀ hR₀
      rw [hR_ρ] at h₁
      calc (R - r) / (2 * R) = (R - r) / 2 / R := by ring
        _ ≤ Real.log (R / ρ) := h₁
    have hlog_pos : (0:ℝ) < (R - r) / (2 * R) := by positivity
    have hN_bound : N ≤ (2 * T + c_f) * (2 * R * (R - r)⁻¹) := by
      have h₁ : N * ((R - r) / (2 * R)) ≤ 2 * T + c_f := by
        calc N * ((R - r) / (2 * R)) ≤ N * Real.log (R / ρ) :=
              mul_le_mul_of_nonneg_left hlog_lb hN₀
          _ ≤ 2 * T + c_f := hN_le
      have h₂ : N ≤ (2 * T + c_f) / ((R - r) / (2 * R)) :=
        (le_div_iff₀ hlog_pos).2 h₁
      apply h₂.trans
      apply le_of_eq
      field_simp
    calc log⁺ N ≤ log⁺ ((2 * T + c_f) * (2 * R * (R - r)⁻¹)) :=
          posLog_le_posLog hN₀ hN_bound
      _ ≤ log⁺ (2 * T + c_f) + log⁺ (2 * R * (R - r)⁻¹) := posLog_mul
      _ ≤ (Real.log 2 + log⁺ (2 * T) + log⁺ c_f)
          + (log⁺ (2 * R) + log⁺ (R - r)⁻¹) := by
          linarith [posLog_add (x := 2 * T) (y := c_f),
            posLog_mul (x := 2 * R) (y := (R - r)⁻¹)]
      _ ≤ 3 * Real.log 2 + log⁺ T + log⁺ c_f + Real.log R + log⁺ (R - r)⁻¹ := by
          have h₁ : log⁺ (2 * T) ≤ Real.log 2 + log⁺ T := by
            calc log⁺ (2 * T) ≤ log⁺ 2 + log⁺ T := posLog_mul
              _ = Real.log 2 + log⁺ T := by rw [posLog_eq_log (by norm_num)]
          have h₂ : log⁺ (2 * R) ≤ Real.log 2 + Real.log R := by
            calc log⁺ (2 * R) ≤ log⁺ 2 + log⁺ R := posLog_mul
              _ = Real.log 2 + Real.log R := by
                  rw [posLog_eq_log (by norm_num),
                    posLog_eq_log (by rw [abs_of_pos hR₀]; linarith)]
          linarith
  -- Bound the argument of `log⁺` in the analytic estimate
  have hX : log⁺ (√K + N * (4 + (ρ - r) ^ (-(2:ℝ)⁻¹)))
      ≤ 10 * Real.log 2 + (3:ℝ)/2 * Real.log R + (5:ℝ)/2 * log⁺ (R - r)⁻¹
        + (3:ℝ)/2 * log⁺ T + (3:ℝ)/2 * log⁺ c_f := by
    have h₁ : log⁺ (√K + N * (4 + (ρ - r) ^ (-(2:ℝ)⁻¹)))
        ≤ Real.log 2 + log⁺ (√K) + log⁺ (N * (4 + (ρ - r) ^ (-(2:ℝ)⁻¹))) := posLog_add
    have h₂ : log⁺ (√K) = 2⁻¹ * log⁺ K := by
      rw [Real.sqrt_eq_rpow, posLog_rpow hK₀ (by norm_num)]
      norm_num
    have h₃ : log⁺ (N * (4 + (ρ - r) ^ (-(2:ℝ)⁻¹)))
        ≤ log⁺ N + log⁺ (4 + (ρ - r) ^ (-(2:ℝ)⁻¹)) := posLog_mul
    have h₄ : log⁺ (4 + (ρ - r) ^ (-(2:ℝ)⁻¹))
        ≤ 3 * Real.log 2 + 2⁻¹ * (Real.log 2 + log⁺ (R - r)⁻¹) := by
      have h₅ : log⁺ (4 + (ρ - r) ^ (-(2:ℝ)⁻¹))
          ≤ Real.log 2 + log⁺ (4:ℝ) + log⁺ ((ρ - r) ^ (-(2:ℝ)⁻¹)) := posLog_add
      have h₆ : log⁺ (4:ℝ) = 2 * Real.log 2 := by
        rw [posLog_eq_log (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      have h₇ : log⁺ ((ρ - r) ^ (-(2:ℝ)⁻¹)) = 2⁻¹ * log⁺ ((ρ - r)⁻¹) := by
        have e₁ : (ρ - r) ^ (-(2:ℝ)⁻¹) = ((ρ - r)⁻¹) ^ ((2:ℝ)⁻¹) := by
          rw [← Real.rpow_neg_one (ρ - r), ← Real.rpow_mul hρr₀.le]
          norm_num
        rw [e₁, posLog_rpow (by positivity) (by norm_num)]
      have h₈ : log⁺ ((ρ - r)⁻¹) ≤ Real.log 2 + log⁺ (R - r)⁻¹ := hpos_inv
      rw [h₆, h₇] at h₅
      have h₉ : 2⁻¹ * log⁺ ((ρ - r)⁻¹) ≤ 2⁻¹ * (Real.log 2 + log⁺ (R - r)⁻¹) := by
        apply mul_le_mul_of_nonneg_left h₈ (by norm_num)
      linarith
    rw [h₂] at h₁
    have h₁₀ : 2⁻¹ * log⁺ K ≤ 2⁻¹ * (5 * Real.log 2 + Real.log R + 2 * log⁺ (R - r)⁻¹
        + log⁺ T + log⁺ c_f) := by
      apply mul_le_mul_of_nonneg_left hlogK (by norm_num)
    linarith
  -- Assemble everything
  have key : proximity (logDeriv f) ⊤ r
      ≤ 3 * log⁺ T + 3 * Real.log R + 5 * log⁺ (R - r)⁻¹ + C₀ := by
    rw [hC₀_def]
    linarith
  have hprod : 0 ≤ C₀ * (log⁺ T + Real.log R + log⁺ (R - r)⁻¹) := by
    apply mul_nonneg hC₀
    linarith [posLog_nonneg (x := T)]
  calc proximity (logDeriv f) ⊤ r
      ≤ 3 * log⁺ T + 3 * Real.log R + 5 * log⁺ (R - r)⁻¹ + C₀ := key
    _ ≤ (5 + C₀) * (log⁺ T + Real.log R + log⁺ (R - r)⁻¹ + 1) := by
        have h₁ := posLog_nonneg (x := T)
        nlinarith [hprod]
