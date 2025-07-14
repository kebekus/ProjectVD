/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import VD.harmonicAt_examples
import VD.harmonicAt_meanValue

/-!
# Representation of `log⁺` as a Circle Average

If `a` is any complex number of norm one, establish that the circle average
`circleAverage (log ‖· - a‖) 0 1` vanishes.

TODO: As soon as the mean value theorem for harmonic functions becomes
available, extend this result to arbitrary complex numbers `a`, showing that the
circle average equals the positive part of the logarithm, `circleAverage (log ‖·
- a‖) 0 1 = = log⁺ ‖a‖`. This result, in turn, is a major ingredient in the
  proof of Jensen's formula in complex analysis.
-/

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

variable {a : ℂ}

/-!
## Lemmas for the circleMap
-/

lemma circleMap_zero_one_add {x₁ x₂ : ℝ} :
    (circleMap 0 1 x₁) * (circleMap 0 1 x₂) = circleMap 0 1 (x₁+x₂) := by
  simp [circleMap, add_mul, Complex.exp_add]

/-!
## Preparatory Lemmas
-/
private lemma norm_circleMap_sub_const_eq_norm_one_sub_circleMapNeg_mul_const {x : ℝ} :
    ‖(circleMap 0 1 x) - a‖ = ‖1 - (circleMap 0 1 (-x)) * a‖ := by
  calc ‖(circleMap 0 1 x) - a‖
  _ = 1 * ‖(circleMap 0 1 x) - a‖ :=
    (one_mul ‖circleMap 0 1 x - a‖).symm
  _ = ‖(circleMap 0 1 (-x))‖ * ‖(circleMap 0 1 x) - a‖ := by
    simp [norm_circleMap_zero]
  _ = ‖(circleMap 0 1 (-x)) * ((circleMap 0 1 x) - a)‖ := by
    exact (Complex.norm_mul (circleMap 0 1 (-x)) (circleMap 0 1 x - a)).symm
  _ = ‖(circleMap 0 1 (-x)) * (circleMap 0 1 x) - (circleMap 0 1 (-x)) * a‖ := by
    rw [mul_sub]
  _ = ‖(circleMap 0 1 0) - (circleMap 0 1 (-x)) * a‖ := by
    rw [circleMap_zero_one_add]
    simp
  _ = ‖1 - (circleMap 0 1 (-x)) * a‖ := by
    congr
    simp [circleMap]

lemma circleAverage_log_norm_id_sub_const_eq_circleAverage_log_norm_one_sub_id_mul_norm_const {a : ℂ} :
    circleAverage (log ‖· - a‖) 0 1 = circleAverage (log ‖1 - · * ‖a‖‖) 0 1 := by
  sorry

/-!
## Computing `circleAverage (log ‖· - a‖) 0 1` in case where `‖a‖ = 1`.
-/

lemma circleAverage_log_norm_id_sub_one_eq_zero :
    ∫ x in (0)..(2 * π), log ‖circleMap 0 1 x - 1‖ = 0 := by
  calc ∫ x in (0)..(2 * π), log ‖circleMap 0 1 x - 1‖
  _ = ∫ x in (0)..(2 * π), log (4 * sin (x / 2) ^ 2) / 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp
    rw [Complex.norm_def, log_sqrt (circleMap 0 1 x - 1).normSq_nonneg]
    congr
    calc Complex.normSq (circleMap 0 1 x - 1)
    _ = (cos x - 1) * (cos x - 1) + sin x * sin x := by
      dsimp [circleMap]
      rw [Complex.normSq_apply]
      simp
    _ = sin x ^ 2 + cos x ^ 2 + 1 - 2 * cos x := by
      ring
    _ = 2 - 2 * cos x := by
      rw [sin_sq_add_cos_sq]
      norm_num
    _ = 2 - 2 * cos (2 * (x / 2)) := by
      rw [← mul_div_assoc]
      congr
      norm_num
    _ = 4 - 4 * cos (x / 2) ^ 2 := by
      rw [cos_two_mul]
      ring
    _ = 4 * sin (x / 2) ^ 2 := by
      nth_rw 1 [← mul_one 4, ← sin_sq_add_cos_sq (x / 2)]
      ring
  _ = ∫ (x : ℝ) in (0)..π, log (4 * sin x ^ 2) := by
    have {x : ℝ} : x / 2 = 2⁻¹ * x := by ring
    rw [intervalIntegral.integral_div, this,
      intervalIntegral.inv_mul_integral_comp_div (f := fun x ↦ log (4 * sin x ^ 2))]
    simp
  _ = ∫ (x : ℝ) in 0..π, log 4 + 2 * log (sin x) := by
    apply intervalIntegral.integral_congr_codiscreteWithin
    apply Filter.codiscreteWithin.mono (by tauto : Ι 0 π ⊆ Set.univ)
    have s₀ : AnalyticOnNhd ℝ (fun x ↦ (4 * sin x ^ 2)) Set.univ := by
      intro x hx
      fun_prop
    have s₁ := s₀.preimage_zero_mem_codiscrete (x := π / 2)
    simp only [sin_pi_div_two, one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      Set.preimage_compl, forall_const] at s₁
    filter_upwards [s₁] with a ha
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, mul_eq_zero,
      OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, false_or] at ha
    rw [log_mul (by norm_num) (by simp_all), log_pow, Nat.cast_ofNat]
  _ = (∫ (x : ℝ) in 0..π, log 4) + 2 * ∫ (x : ℝ) in 0..π, log (sin x) := by
    rw [intervalIntegral.integral_add _root_.intervalIntegrable_const
      (by apply intervalIntegrable_log_sin.const_mul 2), intervalIntegral.integral_const_mul]
  _ = 0 := by
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, integral_log_sin_zero_pi,
      (by norm_num : (4 : ℝ) = 2 * 2), log_mul two_ne_zero two_ne_zero]
    ring

/--
If `‖a‖ = 1`, then `circleAverage (log ‖· - a‖) 0 1 = 0`.
-/
@[simp]
theorem circleAverage_log_norm_sub_id_const_eq_zero'₂ (h : ‖a‖ = 1) :
    circleAverage (log ‖· - a‖) 0 1 = 0 := by
  simp_all only [circleAverage_log_norm_id_sub_const_eq_circleAverage_log_norm_one_sub_id_mul_norm_const]
  unfold circleAverage
  simp only [mul_inv_rev, Complex.ofReal_one, mul_one, smul_eq_mul, mul_eq_zero, inv_eq_zero,
    pi_ne_zero, OfNat.ofNat_ne_zero, or_self, false_or]
  convert circleAverage_log_norm_id_sub_one_eq_zero using 4 with x
  rw [← norm_neg]
  congr
  simp

theorem circleAverage_log_norm_sub_id_const_eq_zero₂ (ha : ‖a‖ = 1) :
  circleAverage (log ‖· - a‖) 0 1 = 0 := by

  simp [circleAverage, pi_ne_zero]

  simp_rw [norm_circleMap_sub_const_eq_norm_one_sub_circleMapNeg_mul_const]
  have {x : ℝ} : log ‖1 - circleMap 0 1 (-x) * a‖ = (log ‖1 - circleMap 0 1 · * a‖) (-x) := by rfl
  conv =>
    left; arg 1; intro x
    rw [this]
  rw [intervalIntegral.integral_comp_neg (log ‖1 - circleMap 0 1 · * a‖)]

  let f₁ := (log ‖1 - circleMap 0 1 · * a‖)
  have {x : ℝ} : log ‖1 - circleMap 0 1 x * a‖ = f₁ (x + 2 * π) := by
    dsimp [f₁]
    congr 4
    let A := periodic_circleMap 0 1 x
    simp at A
    exact id (Eq.symm A)
  conv =>
    left
    arg 1
    intro x
    rw [this]
  rw [intervalIntegral.integral_comp_add_right f₁ (2 * π)]
  simp
  dsimp [f₁]

  have : ∃ ζ, a = circleMap 0 1 ζ := by
    apply Set.exists_range_iff.mp
    use a
    simp
    exact ha
  obtain ⟨ζ, hζ⟩ := this
  rw [hζ]
  simp_rw [circleMap_zero_one_add]

  rw [intervalIntegral.integral_comp_add_right (f := fun x ↦ log (norm (1 - circleMap 0 1 (x))))]

  have : Function.Periodic (fun x ↦ log (norm (1 - circleMap 0 1 x))) (2 * π) := by
    have : (fun x ↦ log (norm (1 - circleMap 0 1 x))) = ( (fun x ↦ log (norm (1 - x))) ∘ (circleMap 0 1) ) := by rfl
    rw [this]
    apply Function.Periodic.comp
    exact periodic_circleMap 0 1

  let A := Function.Periodic.intervalIntegral_add_eq this ζ 0
  simp at A
  simp
  rw [add_comm]
  rw [A]

  have {x : ℝ} : log (norm (1 - circleMap 0 1 x)) = log ‖circleMap 0 1 x - 1‖ := by
    congr 1
    exact norm_sub_rev 1 (circleMap 0 1 x)

  simp_rw [this]
  exact circleAverage_log_norm_id_sub_one_eq_zero


lemma circleAverage_log_norm_sub_id_const_eq_posLog :
    circleAverage (log ‖· - a‖) 0 1 = log⁺ ‖a‖ := by
  rcases lt_trichotomy ‖a‖ 1 with h | h | h
  · -- ‖a‖ < 1
    sorry
  · unfold posLog
    simp_all
  · -- 1 < ‖a‖
    sorry
