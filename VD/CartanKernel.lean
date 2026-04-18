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
    CircleIntegrable (fun a ↦ Real.log ‖z - a‖) c R := by
  convert circleIntegrable_log_norm_sub_const (a := z) (c := c) (r := R) using 1
  funext a
  rw [norm_sub_rev]

end CircleIntegrabilityLemmas

/-! ### Interval-integral swapping -/

section IntervalIntegralSwap

lemma intervalIntegral_swap {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (h_int : Integrable (Function.uncurry f)
        ((volume.restrict (Set.uIoc a b)).prod (volume.restrict (Set.uIoc c d)))) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  have hμ : Set.uIoc a b = Set.Ioc a b := Set.uIoc_of_le hab
  have hν : Set.uIoc c d = Set.Ioc c d := Set.uIoc_of_le hcd
  set μ := volume.restrict (Set.Ioc a b)
  set ν := volume.restrict (Set.Ioc c d)
  have h_int' : Integrable (Function.uncurry f) (μ.prod ν) := by
    simpa [μ, ν, hμ, hν] using h_int
  have h_left :
      ∫ x in a..b, ∫ y in c..d, f x y = ∫ x, ∫ y, f x y ∂ν ∂μ := by
    simp [μ, ν, intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  have h_right :
      ∫ y in c..d, ∫ x in a..b, f x y = ∫ y, ∫ x, f x y ∂μ ∂ν := by
    simp [μ, ν, intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  have h_swap :=
    MeasureTheory.integral_integral_swap (μ := μ) (ν := ν) (f := f) h_int'
  calc
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ x, ∫ y, f x y ∂ν ∂μ := h_left
    _ = ∫ y, ∫ x, f x y ∂μ ∂ν := h_swap
    _ = ∫ y in c..d, ∫ x in a..b, f x y := h_right.symm

end IntervalIntegralSwap

/-! ### Cartan kernel integrability -/

/-- A meromorphic function on `ℂ` is measurable. -/
lemma meromorphicOn_measurable_of_univ {f : ℂ → ℂ} (hf : MeromorphicOn f ⊤) :
    Measurable f := by
  apply measurable_of_isOpen
  intro U hU
  have h_analytic_open : IsOpen {x | AnalyticAt ℂ f x} := isOpen_analyticAt ℂ f
  have h_open_part : IsOpen {x | AnalyticAt ℂ f x ∧ f x ∈ U} := by
    have h_eq : {x | AnalyticAt ℂ f x ∧ f x ∈ U} = {x | AnalyticAt ℂ f x} ∩ f ⁻¹' U := by
      ext x
      simp [Set.mem_inter_iff, Set.mem_preimage]
    rw [h_eq]
    have h_cont : ContinuousOn f {x | AnalyticAt ℂ f x} := by
      intro x hx
      exact hx.continuousAt.continuousWithinAt
    exact h_cont.isOpen_inter_preimage h_analytic_open hU
  have h_poles_countable : Set.Countable {x | ¬AnalyticAt ℂ f x} := by
    have hf' : Meromorphic f := by
      rw [← meromorphicOn_univ]
      simpa using hf
    simpa [Set.mem_setOf_eq] using hf'.countable_compl_analyticAt
  have h_poles_U_countable : Set.Countable {x | ¬AnalyticAt ℂ f x ∧ f x ∈ U} :=
    h_poles_countable.mono fun x hx => hx.1
  have h_decomp :
      f ⁻¹' U = {x | AnalyticAt ℂ f x ∧ f x ∈ U} ∪ {x | ¬AnalyticAt ℂ f x ∧ f x ∈ U} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq]
    tauto
  rw [h_decomp]
  exact h_open_part.measurableSet.union h_poles_U_countable.measurableSet

noncomputable def cartanKernel (f : ℂ → ℂ) (R : ℝ) (α β : ℝ) : ℝ :=
  Real.log ‖f (circleMap 0 R β) - circleMap 0 1 α‖

lemma intervalIntegrable_cartanKernel_in_alpha (f : ℂ → ℂ) (R : ℝ) (β : ℝ) :
    IntervalIntegrable (fun α => cartanKernel f R α β) volume 0 (2 * Real.pi) := by
  simp only [cartanKernel]
  have h_eq : (fun α => Real.log ‖f (circleMap 0 R β) - circleMap 0 1 α‖) =
      fun α => Real.log ‖circleMap 0 1 α - f (circleMap 0 R β)‖ := by
    funext α
    rw [norm_sub_rev]
  rw [h_eq]
  have := circleIntegrable_log_norm_sub_const (a := f (circleMap 0 R β)) (c := 0) (r := 1)
  simpa [CircleIntegrable] using this

lemma integrable_cartanKernel_in_alpha (f : ℂ → ℂ) (R : ℝ) (β : ℝ) :
    Integrable (fun α ↦ cartanKernel f R α β)
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
  have h0_le : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  have h_int :
      IntegrableOn (fun α ↦ cartanKernel f R α β) (Set.Ioc 0 (2 * Real.pi)) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h0_le).1
      (intervalIntegrable_cartanKernel_in_alpha f R β)
  simpa [IntegrableOn] using h_int

lemma integrable_posLog_norm_circleMap {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) {R : ℝ} :
    Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖)
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
  have h0_le : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  have h_circle : CircleIntegrable (fun z ↦ log⁺ ‖f z‖) 0 R :=
    MeromorphicOn.circleIntegrable_posLog_norm (fun x _ ↦ h x trivial)
  unfold CircleIntegrable at h_circle
  rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le h0_le] at h_circle

lemma max_cartanKernel_le (f : ℂ → ℂ) (R α β : ℝ) :
    max (cartanKernel f R α β) 0 ≤ log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2 := by
  calc
    max (cartanKernel f R α β) 0 = log⁺ ‖f (circleMap 0 R β) - circleMap 0 1 α‖ := by
      simp [cartanKernel, Real.posLog_def, max_comm]
    _ = log⁺ ‖f (circleMap 0 R β) + (-circleMap 0 1 α)‖ := by
      rw [sub_eq_add_neg]
    _ ≤ log⁺ ‖f (circleMap 0 R β)‖ + log⁺ ‖-circleMap 0 1 α‖ + Real.log 2 := by
      simpa using posLog_norm_add_le (f (circleMap 0 R β)) (-circleMap 0 1 α)
    _ = log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2 := by
      simp [norm_circleMap_zero, add_comm]

lemma integral_norm_eq_two_mul_integral_max_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : Integrable g μ) (hmax : Integrable (fun x ↦ max (g x) 0) μ) :
    ∫ x, ‖g x‖ ∂μ = 2 * ∫ x, max (g x) 0 ∂μ - ∫ x, g x ∂μ := by
  have h_eq : ∀ x, ‖g x‖ = 2 * max (g x) 0 - g x := by
    intro x
    by_cases hx : 0 ≤ g x
    · rw [Real.norm_eq_abs, abs_of_nonneg hx, max_eq_left hx]
      ring
    · rw [Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hx),
        max_eq_right (le_of_lt (lt_of_not_ge hx))]
      ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_eq), integral_sub]
  · simp [integral_const_mul]
  · exact hmax.const_mul 2
  · exact hg

lemma intervalIntegral_cartanKernel_eq_two_pi_mul_posLog (f : ℂ → ℂ) (R β : ℝ) :
    ∫ α in (0 : ℝ)..2 * Real.pi, cartanKernel f R α β =
      (2 * Real.pi) * log⁺ ‖f (circleMap 0 R β)‖ := by
  let z := f (circleMap 0 R β)
  have h_avg : circleAverage (fun a ↦ Real.log ‖z - a‖) 0 1 = log⁺ ‖z‖ := by
    have h_eq : (fun a ↦ Real.log ‖z - a‖) = fun a ↦ Real.log ‖a - z‖ := by
      funext a
      rw [norm_sub_rev]
    rw [h_eq]
    exact circleAverage_log_norm_sub_const_eq_posLog (a := z)
  rw [Real.circleAverage_def] at h_avg
  simp only [smul_eq_mul] at h_avg
  have h_two_pi : (2 * Real.pi) ≠ 0 := by positivity
  field_simp [h_two_pi] at h_avg
  simpa [z, cartanKernel] using h_avg

lemma measurable_cartanKernel {f : ℂ → ℂ} (hf : Measurable f) {R : ℝ} :
    Measurable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2) := by
  have h_meas_G1 : Measurable (fun p : ℝ × ℝ => f (circleMap 0 R p.2)) :=
    hf.comp ((continuous_circleMap 0 R).measurable.comp measurable_snd)
  have h_meas_G2 : Measurable (fun p : ℝ × ℝ => circleMap 0 1 p.1) :=
    (continuous_circleMap 0 1).measurable.comp measurable_fst
  exact Real.measurable_log.comp <|
    continuous_norm.measurable.comp <| h_meas_G1.sub h_meas_G2

/-- Bound on the positive part of an angular slice of the Cartan kernel. -/
lemma integral_max_cartanKernel_le (f : ℂ → ℂ) (R β : ℝ) :
    ∫ α, max (cartanKernel f R α β) 0 ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) ≤
      (2 * Real.pi) * (log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2) := by
  let z := f (circleMap 0 R β)
  have h_int_le :
      ∫ α, max (cartanKernel f R α β) 0 ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) ≤
        ∫ _ : ℝ, log⁺ ‖z‖ + Real.log 2 ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun _ => le_max_right _ _
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun α ↦ by simpa [z] using max_cartanKernel_le f R α β
  have h_int_const :
      ∫ _ : ℝ, log⁺ ‖z‖ + Real.log 2 ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) =
        (log⁺ ‖z‖ + Real.log 2) * (2 * Real.pi) := by
    rw [integral_const, smul_eq_mul, mul_comm, measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le Real.two_pi_pos.le, sub_zero]
  rw [h_int_const] at h_int_le
  simpa [z, mul_comm] using h_int_le

/-- Formula for the `L¹` norm of an angular slice of the Cartan kernel. -/
lemma integral_norm_cartanKernel_eq (f : ℂ → ℂ) (R β : ℝ) :
    ∫ α, ‖cartanKernel f R α β‖ ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) =
      2 * (∫ α, max (cartanKernel f R α β) 0 ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi)))) -
        (2 * Real.pi) * log⁺ ‖f (circleMap 0 R β)‖ := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))
  change ∫ α, ‖cartanKernel f R α β‖ ∂μ =
    2 * (∫ α, max (cartanKernel f R α β) 0 ∂μ) - (2 * Real.pi) * log⁺ ‖f (circleMap 0 R β)‖
  have h_slice : Integrable (fun α ↦ cartanKernel f R α β) μ := by
    simpa [μ] using integrable_cartanKernel_in_alpha f R β
  have h_slice_max : Integrable (fun α ↦ max (cartanKernel f R α β) 0) μ :=
    h_slice.sup (integrable_const 0)
  have h_kernel :
      ∫ α, cartanKernel f R α β ∂μ = (2 * Real.pi) * log⁺ ‖f (circleMap 0 R β)‖ := by
    calc
      ∫ α, cartanKernel f R α β ∂μ
          = ∫ α in (0 : ℝ)..2 * Real.pi, cartanKernel f R α β := by
              simpa [μ] using
                integral_restrict_Ioc_eq_intervalIntegral
                  (f := fun α ↦ cartanKernel f R α β) Real.two_pi_pos.le
      _ = (2 * Real.pi) * log⁺ ‖f (circleMap 0 R β)‖ :=
            intervalIntegral_cartanKernel_eq_two_pi_mul_posLog f R β
  calc
    ∫ α, ‖cartanKernel f R α β‖ ∂μ
        = 2 * (∫ α, max (cartanKernel f R α β) 0 ∂μ) - ∫ α, cartanKernel f R α β ∂μ := by
            simpa using
              integral_norm_eq_two_mul_integral_max_sub
                (g := fun α ↦ cartanKernel f R α β) h_slice h_slice_max
    _ = 2 * (∫ α, max (cartanKernel f R α β) 0 ∂μ) -
          (2 * Real.pi) * log⁺ ‖f (circleMap 0 R β)‖ := by
            rw [h_kernel]

/-- The `L¹` norms of the angular slices of the Cartan kernel form an integrable family. -/
lemma integrable_integral_norm_cartanKernel {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) {R : ℝ} :
    Integrable
      (fun β ↦ ∫ α, ‖cartanKernel f R α β‖ ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))))
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))
  have h_meas_K : Measurable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2) :=
    measurable_cartanKernel (meromorphicOn_measurable_of_univ h)
  have h_int_posLog : Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖) μ := by
    simpa [μ] using integrable_posLog_norm_circleMap h (R := R)
  have h_int_Term2 : Integrable (fun β ↦ (2 * Real.pi) * log⁺ ‖f (circleMap 0 R β)‖) μ :=
    h_int_posLog.const_mul (2 * Real.pi)
  have h_int_Bound : Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2) μ :=
    h_int_posLog.add (integrable_const (Real.log 2))
  have h_int_Term1 : Integrable (fun β ↦ ∫ α, max (cartanKernel f R α β) 0 ∂μ) μ := by
    refine Integrable.mono (h_int_Bound.const_mul (2 * Real.pi)) ?_ ?_
    · exact
        (h_meas_K.max measurable_const).stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    · filter_upwards with β
      have h_int_nonneg : 0 ≤ ∫ α, max (cartanKernel f R α β) 0 ∂μ :=
        integral_nonneg fun _ => le_max_right _ _
      have h_bound_nonneg : 0 ≤ (2 * Real.pi) * (log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2) := by
        apply mul_nonneg (by linarith [Real.two_pi_pos])
        apply add_nonneg Real.posLog_nonneg
        exact Real.log_nonneg (by norm_num)
      rw [Real.norm_of_nonneg h_int_nonneg, Real.norm_of_nonneg h_bound_nonneg]
      simpa [μ] using integral_max_cartanKernel_le f R β
  refine Integrable.congr ((h_int_Term1.const_mul 2).sub h_int_Term2) ?_
  exact Filter.Eventually.of_forall fun β ↦ by
    simpa [μ] using (integral_norm_cartanKernel_eq f R β).symm

lemma circleAverage_eq_integral_cartanKernel_left (f : ℂ → ℂ) (R α : ℝ) :
    circleAverage (fun z ↦ Real.log ‖f z - circleMap 0 1 α‖) 0 R =
      (2 * Real.pi)⁻¹ * ∫ β in (0 : ℝ)..2 * Real.pi, cartanKernel f R α β := by
  simp [Real.circleAverage, cartanKernel]

lemma integral_cartanKernel_eq_circleAverage_right (f : ℂ → ℂ) (R β : ℝ) :
    (2 * Real.pi)⁻¹ * ∫ α in (0 : ℝ)..2 * Real.pi, cartanKernel f R α β =
      circleAverage (fun a : ℂ ↦ Real.log ‖f (circleMap 0 R β) - a‖) 0 1 := by
  simp [Real.circleAverage, cartanKernel]

lemma integrable_intervalIntegral_cartanKernel_left {f : ℂ → ℂ} {R : ℝ}
    (h_int :
      Integrable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2)
        ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod
         (volume.restrict (Set.uIoc 0 (2 * Real.pi))))) :
    Integrable (fun α => ∫ β in (0 : ℝ)..2 * Real.pi, cartanKernel f R α β)
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
  have h0_le : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  rw [Set.uIoc_of_le h0_le] at h_int
  simpa [intervalIntegral.integral_of_le h0_le, cartanKernel] using h_int.integral_prod_left

lemma cartan_integrability {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) {R : ℝ} :
    Integrable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod
       (volume.restrict (Set.uIoc 0 (2 * Real.pi)))) := by
  have hIoc : Set.uIoc 0 (2 * Real.pi) = Set.Ioc 0 (2 * Real.pi) := Set.uIoc_of_le Real.two_pi_pos.le
  simp only [hIoc]
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))
  have h_sm_K : StronglyMeasurable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2) :=
    (measurable_cartanKernel (meromorphicOn_measurable_of_univ h)).stronglyMeasurable
  have h_aesm_K :
      AEStronglyMeasurable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2) (μ.prod μ) :=
    h_sm_K.aestronglyMeasurable
  refine (integrable_prod_iff' h_aesm_K).2 ?_
  refine ⟨Filter.Eventually.of_forall ?_, ?_⟩
  · intro β
    simpa [μ] using integrable_cartanKernel_in_alpha f R β
  · simpa [μ] using integrable_integral_norm_cartanKernel h (R := R)

lemma cartan_swap_averages_aux
    {f : ℂ → ℂ} {R : ℝ}
    (h_int_kernel :
      Integrable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2)
        ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod
         (volume.restrict (Set.uIoc 0 (2 * Real.pi))))) :
    circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1 =
      circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R := by
  let F : ℝ → ℝ → ℝ := cartanKernel f R
  have h0_le : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  have h_swap :
      ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β =
        ∫ β in 0..2 * Real.pi, ∫ α in 0..2 * Real.pi, F α β :=
    intervalIntegral_swap h0_le h0_le (by simpa [F, cartanKernel] using h_int_kernel)
  calc
    circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
        = (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ *
            ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β := by
            simp [Real.circleAverage, F, mul_comm, mul_left_comm, mul_assoc]
            aesop
    _ = (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ *
          ∫ β in 0..2 * Real.pi, ∫ α in 0..2 * Real.pi, F α β := by
            rw [h_swap]
    _ = (2 * Real.pi)⁻¹ *
          ∫ β in 0..2 * Real.pi, ((2 * Real.pi)⁻¹ * ∫ α in 0..2 * Real.pi, F α β) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (2 * Real.pi)⁻¹ * ∫ β in 0..2 * Real.pi, log⁺ ‖f (circleMap 0 R β)‖ := by
          congr 1
          apply intervalIntegral.integral_congr
          intro β hβ
          calc
            (2 * Real.pi)⁻¹ * ∫ α in 0..2 * Real.pi, F α β
                = circleAverage (fun a : ℂ ↦ Real.log ‖f (circleMap 0 R β) - a‖) 0 1 := by
                    simpa [F] using integral_cartanKernel_eq_circleAverage_right f R β
            _ = log⁺ ‖f (circleMap 0 R β)‖ := by
                  have h_eq :
                      (fun a ↦ Real.log ‖f (circleMap 0 R β) - a‖) =
                        fun a ↦ Real.log ‖a - f (circleMap 0 R β)‖ := by
                    funext a
                    rw [norm_sub_rev]
                  rw [h_eq]
                  exact
                    circleAverage_log_norm_sub_const_eq_posLog (a := f (circleMap 0 R β))
    _ = circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R := by
          simp [Real.circleAverage, intervalIntegral.integral_of_le Real.two_pi_pos.le]

/-- Auxiliary Fubini step used in the proof of Cartan's formula. -/
lemma cartan_swap_averages {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) {R : ℝ} :
    circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1 =
      circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R :=
  cartan_swap_averages_aux (cartan_integrability h)

/-- Auxiliary circle-integrability statement used to average Cartan's identity in the value
variable. -/
lemma circleIntegrable_circleAverage_log_norm_sub_unit {f : ℂ → ℂ}
    (h : MeromorphicOn f ⊤) {R : ℝ} :
    CircleIntegrable (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1 := by
  by_cases hR : R = 0
  · subst hR
    have h_eq : (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 0) =
        fun a ↦ Real.log ‖f 0 - a‖ := by
      funext a
      simp [circleAverage_zero]
    rw [h_eq]
    exact circleIntegrable_log_norm_sub (f 0) 0 1
  have h0_le : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  have h_int :
      Integrable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2)
        ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod
         (volume.restrict (Set.uIoc 0 (2 * Real.pi)))) :=
    cartan_integrability (f := f) (R := R) h
  unfold CircleIntegrable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h0_le]
  apply IntegrableOn.congr_fun
    ((integrable_intervalIntegral_cartanKernel_left (f := f) (R := R) h_int).const_mul (2 * Real.pi)⁻¹)
    _ measurableSet_Ioc
  intro α _
  exact (circleAverage_eq_integral_cartanKernel_left f R α).symm

end Cartan
end ValueDistribution
