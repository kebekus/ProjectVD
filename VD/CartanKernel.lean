/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Stefan Kebekus
-/

module

public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

public section

open Filter Function Metric Real Set Classical Topology ValueDistribution
open MeasureTheory
open scoped Real Topology MeasureTheory Metric

/-!
# Cartan Kernel Estimates

This file contains the measure-theoretic support for Cartan's formula.

## Main statements

- `ValueDistribution.Cartan.cartan_swap_averages`
- `ValueDistribution.Cartan.circleIntegrable_circleAverage_log_norm_sub_unit`

## Implementation notes

The file provides the Fubini and integrability argument for the Cartan kernel into
auxiliary lemmas in the namespace `ValueDistribution.Cartan`. They are used by
`VD/Cartan.lean` and `VD/CartanTrailing.lean`.

-/

namespace ValueDistribution
namespace Cartan

/-! ### General integration lemmas -/

section

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma integral_restrict_eq_setIntegral {μ : Measure α} {s : Set α} (f : α → E) :
    ∫ x, f x ∂μ.restrict s = ∫ x in s, f x ∂μ := rfl

lemma uIoc_zero_eq_Ioc {a : ℝ} (ha : 0 ≤ a) : Set.uIoc 0 a = Set.Ioc 0 a := by
  simp [Set.uIoc_of_le ha]

lemma integral_restrict_Ioc_eq_intervalIntegral {f : ℝ → E} {a : ℝ} (ha : 0 ≤ a) :
    ∫ x, f x ∂volume.restrict (Set.Ioc 0 a) = ∫ x in 0..a, f x := by
  rw [integral_restrict_eq_setIntegral]
  exact (intervalIntegral.integral_of_le ha).symm

end

/-! ### Circle-integrability wrappers -/

section CircleIntegrabilityLemmas

/-- Auxiliary criterion for circle integrability from constancy on the circle. -/
lemma circleIntegrable_of_const_on_sphere
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} {c : ℂ} {R : ℝ} {C : E}
    (h_eq : ∀ a ∈ Metric.sphere c |R|, f a = C) :
    CircleIntegrable f c R := by
  have h_param_eq : ∀ θ, f (circleMap c R θ) = C := by
    intro θ
    apply h_eq
    simp [mem_sphere_iff_norm, circleMap_sub_center]
  unfold CircleIntegrable
  simp [h_param_eq, intervalIntegrable_const]

/-- Auxiliary wrapper phrased in terms of `z - a`. -/
lemma circleIntegrable_log_norm_sub (z c : ℂ) (R : ℝ) :
    CircleIntegrable (fun a ↦ log ‖z - a‖) c R := by
  convert circleIntegrable_log_norm_sub_const (a := z) (c := c) (r := R) using 1
  funext a
  rw [norm_sub_rev]

end CircleIntegrabilityLemmas

/-! ### Cartan kernel integrability -/

noncomputable def cartanKernel (f : ℂ → ℂ) (R : ℝ) (α β : ℝ) : ℝ :=
  log ‖f (circleMap 0 R β) - circleMap 0 1 α‖

lemma integrable_cartanKernel_in_alpha (f : ℂ → ℂ) (R : ℝ) (β : ℝ) :
    Integrable (cartanKernel f R · β)
      (volume.restrict (Set.Ioc 0 (2 * π))) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1
  simpa [cartanKernel, norm_sub_rev, CircleIntegrable] using circleIntegrable_log_norm_sub_const 1

lemma max_cartanKernel_le (f : ℂ → ℂ) (R α β : ℝ) :
    max (cartanKernel f R α β) 0 ≤ log⁺ ‖f (circleMap 0 R β)‖ + log 2 := by
  calc max (cartanKernel f R α β) 0
    _ = log⁺ ‖f (circleMap 0 R β) - circleMap 0 1 α‖ := by
      simp [cartanKernel, posLog_def, max_comm]
    _ = log⁺ ‖f (circleMap 0 R β) + (-circleMap 0 1 α)‖ := by
      rw [sub_eq_add_neg]
    _ ≤ log⁺ ‖f (circleMap 0 R β)‖ + log⁺ ‖-circleMap 0 1 α‖ + log 2 := by
      simpa using posLog_norm_add_le (f (circleMap 0 R β)) (-circleMap 0 1 α)
    _ = log⁺ ‖f (circleMap 0 R β)‖ + log 2 := by
      simp [norm_circleMap_zero, add_comm]

lemma integral_norm_eq_two_mul_integral_max_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : Integrable g μ) (hmax : Integrable (fun x ↦ max (g x) 0) μ) :
    ∫ x, ‖g x‖ ∂μ = 2 * ∫ x, max (g x) 0 ∂μ - ∫ x, g x ∂μ := by
  have h_eq : ∀ x, ‖g x‖ = 2 * max (g x) 0 - g x := by
    intro x
    by_cases hx : 0 ≤ g x
    · rw [norm_eq_abs, abs_of_nonneg hx, max_eq_left hx]
      ring
    · rw [norm_eq_abs, abs_of_neg (lt_of_not_ge hx),
        max_eq_right (le_of_lt (lt_of_not_ge hx))]
      ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_eq), integral_sub (hmax.const_mul 2) hg,
    integral_const_mul]

lemma measurable_cartanKernel {f : ℂ → ℂ} (hf : Measurable f) {R : ℝ} :
    Measurable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2) := by
  apply measurable_log.comp (continuous_norm.measurable.comp _)
  exact (hf.comp ((continuous_circleMap 0 R).measurable.comp measurable_snd)).sub
    ((continuous_circleMap 0 1).measurable.comp measurable_fst)

/-- Formula for the `L¹` norm of an angular slice of the Cartan kernel. -/
lemma integral_norm_cartanKernel_eq (f : ℂ → ℂ) (R β : ℝ) :
    ∫ α, ‖cartanKernel f R α β‖ ∂(volume.restrict (Set.Ioc 0 (2 * π))) =
      2 * (∫ α, max (cartanKernel f R α β) 0 ∂(volume.restrict (Set.Ioc 0 (2 * π)))) -
        (2 * π) * log⁺ ‖f (circleMap 0 R β)‖ := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * π))
  have h_kernel :
      ∫ α, cartanKernel f R α β ∂μ = (2 * π) * log⁺ ‖f (circleMap 0 R β)‖ := by
    calc ∫ α, cartanKernel f R α β ∂μ
      _ = ∫ α in (0 : ℝ)..2 * π, cartanKernel f R α β :=
        integral_restrict_Ioc_eq_intervalIntegral two_pi_pos.le
      _ = (2 * π) * log⁺ ‖f (circleMap 0 R β)‖ := by
        let z := f (circleMap 0 R β)
        have h_avg : circleAverage (log ‖z - ·‖) 0 1 = log⁺ ‖z‖ := by
          simp_rw [norm_sub_rev]
          exact circleAverage_log_norm_sub_const_eq_posLog
        simp only [circleAverage_def, smul_eq_mul] at h_avg
        field_simp [two_pi_pos.ne'] at h_avg
        simpa using h_avg
  calc ∫ α, ‖cartanKernel f R α β‖ ∂μ
    _ = 2 * (∫ α, max (cartanKernel f R α β) 0 ∂μ) - ∫ α, cartanKernel f R α β ∂μ := by
      have h_slice : Integrable (cartanKernel f R · β) μ :=
        integrable_cartanKernel_in_alpha f R β
      exact integral_norm_eq_two_mul_integral_max_sub h_slice (h_slice.sup (integrable_const 0))
    _ = 2 * (∫ α, max (cartanKernel f R α β) 0 ∂μ) - (2 * π) * log⁺ ‖f (circleMap 0 R β)‖ := by
      rw [h_kernel]

/-- The `L¹` norms of the angular slices of the Cartan kernel form an integrable family. -/
lemma integrable_integral_norm_cartanKernel {f : ℂ → ℂ} (h : Meromorphic f) {R : ℝ} :
    Integrable
      (∫ α, ‖cartanKernel f R α ·‖ ∂(volume.restrict (Set.Ioc 0 (2 * π))))
      (volume.restrict (Set.Ioc 0 (2 * π))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * π))
  have h_meas_K : Measurable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2) :=
    measurable_cartanKernel h.measurable
  have h_int_posLog : Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖) μ := by
    have : CircleIntegrable (log⁺ ‖f ·‖) 0 R :=
      h.meromorphicOn.circleIntegrable_posLog_norm
    rwa [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le] at this
  have h_int_Bound : Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖ + log 2) μ :=
    h_int_posLog.add (integrable_const (log 2))
  have h_int_Term1 : Integrable (fun β ↦ ∫ α, max (cartanKernel f R α β) 0 ∂μ) μ := by
    refine Integrable.mono (h_int_Bound.const_mul (2 * π)) ?_ ?_
    · exact
        (h_meas_K.max measurable_const).stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    · filter_upwards with β
      have h_int_nonneg : 0 ≤ ∫ α, max (cartanKernel f R α β) 0 ∂μ :=
        integral_nonneg fun _ ↦ le_max_right _ _
      have h_bound_nonneg : 0 ≤ (2 * π) * (log⁺ ‖f (circleMap 0 R β)‖ + log 2) := by
        apply mul_nonneg (by linarith [two_pi_pos])
        apply add_nonneg posLog_nonneg (log_nonneg (by norm_num))
      rw [norm_of_nonneg h_int_nonneg, norm_of_nonneg h_bound_nonneg]
      have : ∫ α, max (cartanKernel f R α β) 0 ∂(volume.restrict (Set.Ioc 0 (2 * π))) ≤
          ∫ _, log⁺ ‖f (circleMap 0 R β)‖ + log 2 ∂(volume.restrict (Set.Ioc 0 (2 * π))) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun _ ↦ le_max_right _ _
        · exact integrable_const _
        · exact Filter.Eventually.of_forall (max_cartanKernel_le f R · β)
      rwa [integral_const, smul_eq_mul, mul_comm, measureReal_restrict_apply_univ,
        mul_comm, volume_real_Ioc_of_le two_pi_pos.le, sub_zero] at this
  exact Integrable.congr ((h_int_Term1.const_mul 2).sub (h_int_posLog.const_mul (2 * π)))
    (Filter.Eventually.of_forall fun β ↦ (integral_norm_cartanKernel_eq f R β).symm)

lemma cartan_integrability {f : ℂ → ℂ} (h : Meromorphic f) {R : ℝ} :
    Integrable (fun p ↦ cartanKernel f R p.1 p.2)
      ((volume.restrict (Set.uIoc 0 (2 * π))).prod
       (volume.restrict (Set.uIoc 0 (2 * π)))) := by
  simpa [Set.uIoc_of_le two_pi_pos.le] using (integrable_prod_iff'
    (measurable_cartanKernel h.measurable).stronglyMeasurable.aestronglyMeasurable).2
    ⟨Filter.Eventually.of_forall (integrable_cartanKernel_in_alpha f R),
      integrable_integral_norm_cartanKernel h⟩

/-- Auxiliary Fubini step used in the proof of Cartan's formula. -/
lemma cartan_swap_averages {f : ℂ → ℂ} (h : Meromorphic f) {R : ℝ} :
    circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R) 0 1 =
      circleAverage (log⁺ ‖f ·‖) 0 R :=
  let F : ℝ → ℝ → ℝ := cartanKernel f R
  calc circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R) 0 1
    _ = (2 * π)⁻¹ * (2 * π)⁻¹ * ∫ α in 0..2 * π, ∫ β in 0..2 * π, F α β := by
      simp only [circleAverage, mul_comm, mul_inv_rev, smul_eq_mul, mul_assoc,
        intervalIntegral.integral_const_mul, mul_left_comm, mul_eq_mul_left_iff, inv_eq_zero,
        OfNat.ofNat_ne_zero, or_false, pi_ne_zero, F]
      aesop
    _ = (2 * π)⁻¹ * (2 * π)⁻¹ * ∫ β in 0..2 * π, ∫ α in 0..2 * π, F α β := by
      have intervalIntegral_swap {f : ℝ → ℝ → ℝ}
        (h_int : Integrable (Function.uncurry f)
            ((volume.restrict (Set.uIoc 0 (2 * π))).prod (volume.restrict (Set.uIoc 0 (2 * π))))) :
        ∫ x in 0..2 * π, ∫ y in 0..2 * π, f x y = ∫ y in 0..2 * π, ∫ x in 0..2 * π, f x y := by
        set μ := volume.restrict (Set.Ioc 0 (2 * π))
        set ν := volume.restrict (Set.Ioc 0 (2 * π))
        calc ∫ x in 0..2 * π, ∫ y in 0..2 * π, f x y
          _ = ∫ x, ∫ y, f x y ∂ν ∂μ := by
            simp [μ, ν, intervalIntegral.integral_of_le two_pi_pos.le]
          _ = ∫ y, ∫ x, f x y ∂μ ∂ν := by
            apply MeasureTheory.integral_integral_swap
            simpa [μ, ν, Set.uIoc_of_le two_pi_pos.le] using h_int
          _ = ∫ y in 0..2 * π, ∫ x in 0..2 * π, f x y := by
            simp [μ, ν, intervalIntegral.integral_of_le two_pi_pos.le]
      rw [intervalIntegral_swap (by simpa [F, cartanKernel]
        using (cartan_integrability h))]
    _ = (2 * π)⁻¹ * ∫ β in 0..2 * π, ((2 * π)⁻¹ * ∫ α in 0..2 * π, F α β) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (2 * π)⁻¹ * ∫ β in 0..2 * π, log⁺ ‖f (circleMap 0 R β)‖ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro β hβ
      calc (2 * π)⁻¹ * ∫ α in 0..2 * π, F α β
        _ = circleAverage (fun a ↦ log ‖f (circleMap 0 R β) - a‖) 0 1 := by
          simp [F, circleAverage, cartanKernel]
        _ = log⁺ ‖f (circleMap 0 R β)‖ := by
          simp [norm_sub_rev]
    _ = circleAverage (log⁺ ‖f ·‖) 0 R := by
      simp [circleAverage, intervalIntegral.integral_of_le two_pi_pos.le]

/-- Auxiliary circle-integrability statement used to average Cartan's identity in the value
variable. -/
lemma circleIntegrable_circleAverage_log_norm_sub_unit {f : ℂ → ℂ}
    (h : Meromorphic f) {R : ℝ} :
    CircleIntegrable (fun a ↦ circleAverage (log ‖f · - a‖) 0 R) 0 1 := by
  by_cases hR : R = 0
  · simpa [hR, circleAverage_zero] using circleIntegrable_log_norm_sub (f 0) 0 1
  have integrable_intervalIntegral_cartanKernel_left :
      Integrable (∫ β in 0..2 * π, cartanKernel f R · β)
        (volume.restrict (Set.Ioc 0 (2 * π))) := by
    have h_int := cartan_integrability (R := R) h
    rw [Set.uIoc_of_le two_pi_pos.le] at h_int
    simpa [intervalIntegral.integral_of_le two_pi_pos.le, cartanKernel]
      using h_int.integral_prod_left
  unfold CircleIntegrable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le]
  apply IntegrableOn.congr_fun
    (integrable_intervalIntegral_cartanKernel_left.const_mul (2 * π)⁻¹)
    (fun _ _ ↦ by simp [circleAverage, cartanKernel]) measurableSet_Ioc

end Cartan
end ValueDistribution
