/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Stefan Kebekus
-/

module

public import VD.CartanKernel

public section

open Filter Function Metric Real Set Classical Topology ValueDistribution
open scoped Real Topology MeasureTheory Metric

/-!
# Cartan Trailing-Coefficient Estimates

This file isolates the trailing-coefficient terms that appear before the final averaging step in
Cartan's formula.

## Main statements

- `ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_log_trailingCoeff`
- `ValueDistribution.Cartan.logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top`
- `ValueDistribution.Cartan.circleAverage_log_trailingCoeff_eq_zero`

## Implementation notes

The root theorem is a Jensen / First Main Theorem reformulation. The auxiliary lemmas in
`ValueDistribution.Cartan` specialize that identity to `f - a` and analyze the corresponding
trailing-coefficient averages that appear in `VD/Cartan.lean`.

## References

* [S. Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677]

## Tags

Cartan, Nevanlinna theory, trailing coefficient, log counting
-/

namespace ValueDistribution

/-- Jensen-type identity relating zeros and poles: for a meromorphic `f` on the plane, the
difference of counting functions at `0` and at `⊤` equals a circle average minus the logarithm of
the first nonzero Laurent coefficient at `0`. This is the one-variable input used later in
Cartan's formula. -/
private theorem logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_log_trailingCoeff
    {f : ℂ → ℂ} (hf : Meromorphic f) {R : ℝ} (hR : R ≠ 0) :
    logCounting f 0 R - logCounting f ⊤ R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have h_eval :
      circleAverage (log ‖f ·‖) 0 R
        - (MeromorphicOn.divisor f Set.univ).logCounting R =
        log ‖meromorphicTrailingCoeffAt f 0‖ := by
    exact
      (congrArg (fun F ↦ F R)
          (ValueDistribution.characteristic_sub_characteristic_inv (f := f) (h := hf))).symm.trans
        (ValueDistribution.characteristic_sub_characteristic_inv_of_ne_zero
          (f := f) (hf := hf) (hR := hR))
  have h_div :
      (MeromorphicOn.divisor f Set.univ).logCounting R = logCounting f 0 R - logCounting f ⊤ R :=
    congrArg (fun F ↦ F R) (ValueDistribution.log_counting_zero_sub_logCounting_top (f := f))
  calc
    logCounting f 0 R - logCounting f ⊤ R
        = (MeromorphicOn.divisor f Set.univ).logCounting R := by
          simpa using h_div.symm
    _ = circleAverage (fun z ↦ log ‖f z‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
          linarith

namespace Cartan

private lemma norm_eq_one_of_mem_unitSphere {a : ℂ}
    (ha : a ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|) : ‖a‖ = 1 := by
  simpa [Metric.mem_sphere, abs_one] using ha

private lemma ne_zero_of_mem_unitSphere {a : ℂ}
    (ha : a ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|) : a ≠ 0 := by
  intro h0
  simpa [h0] using norm_eq_one_of_mem_unitSphere ha

private lemma meromorphicTrailingCoeffAt_eq_of_tendsto_order_eq_zero {g : ℂ → ℂ}
    (hg : MeromorphicAt g 0) (hord : meromorphicOrderAt g 0 = 0)
    {L : ℂ} (hL : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 L)) :
    meromorphicTrailingCoeffAt g 0 = L := by
  have htrailing : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (meromorphicTrailingCoeffAt g 0)) := by
    simpa [hord] using MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt (h := hg)
  exact tendsto_nhds_unique'
    (X := ℂ) (Y := ℂ) (l := 𝓝[≠] (0 : ℂ))
    (a := meromorphicTrailingCoeffAt g 0) (b := L)
    (by infer_instance) htrailing hL

/-- Specialized version of the Jensen-type identity for `g := f - a`. -/
lemma logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top
    {f : ℂ → ℂ} (h : Meromorphic f) {R : ℝ} (hR : R ≠ 0) (a : ℂ) :
    logCounting f a R + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ =
      circleAverage (fun z ↦ log ‖f z - a‖) 0 R + logCounting f ⊤ R := by
  have hg : Meromorphic (f · - a) := h.sub (Meromorphic.const a)
  have h_meromorphic : Meromorphic f := by
    rw [← meromorphicOn_univ]
    simpa using h
  have hg' : Meromorphic (f · - a) := by
    rw [← meromorphicOn_univ]
    simpa using hg
  have h_zero :
      logCounting (f · - a) 0 = logCounting f (a : WithTop ℂ) := by
    simpa using
      (ValueDistribution.logCounting_coe_eq_logCounting_sub_const_zero (f := f) (a₀ := a)).symm
  have h_top :
      logCounting (f · - a) ⊤ = logCounting f ⊤ :=
    ValueDistribution.logCounting_sub_const (f := f) (a₀ := a) (hf := h_meromorphic)
  have hJ :
      logCounting f a R - logCounting f ⊤ R =
        circleAverage (fun z ↦ log ‖f z - a‖) 0 R -
          log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ := by
    simpa [h_zero, h_top] using
      (logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_log_trailingCoeff
        (f := fun z ↦ f z - a) (hf := hg') (R := R) hR)
  linarith

/-- If `f` has a zero at the origin, then subtracting a nonzero constant shifts the trailing
coefficient of `f` at `0` to that constant term. -/
private lemma meromorphicTrailingCoeff_sub_const_eq_neg {f : ℂ → ℂ}
    (h : Meromorphic f) (h₂ : 0 < meromorphicOrderAt f 0) {a : ℂ} (ha : a ≠ 0) :
    meromorphicTrailingCoeffAt (f · - a) 0 = -a := by
  let g : ℂ → ℂ := fun z ↦ f z - a
  have hmero_g : MeromorphicAt g 0 := (h.sub (Meromorphic.const a)) 0
  have h_tendsto0 : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_zero_of_meromorphicOrderAt_pos (f := f) (x := 0) h₂
  have h_tendsto_g : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (-a)) := by
    have := (Filter.tendsto_sub_const_iff (G := ℂ) (b := a) (c := (0 : ℂ))
      (f := f) (l := 𝓝[≠] (0 : ℂ))).2 h_tendsto0
    simpa [g, sub_eq_add_neg] using this
  have h_ord : meromorphicOrderAt g 0 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hf := hmero_g)).mp
      ⟨-a, by simp [ha], h_tendsto_g⟩
  simpa [g] using
    meromorphicTrailingCoeffAt_eq_of_tendsto_order_eq_zero hmero_g h_ord h_tendsto_g

private lemma log_trailingCoeff_eq_zero_on_unitSphere {f : ℂ → ℂ}
    (h : Meromorphic f) (h₂ : 0 < meromorphicOrderAt f 0) :
    ∀ a ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|,
      log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ = (0 : ℝ) := by
  intro a ha
  rw [meromorphicTrailingCoeff_sub_const_eq_neg h h₂ (ne_zero_of_mem_unitSphere ha)]
  simp [norm_eq_one_of_mem_unitSphere ha]

/-- If `f` has a zero at the origin, then the trailing-coefficient correction term vanishes after
averaging over the unit circle. -/
lemma circleAverage_log_trailingCoeff_eq_zero {f : ℂ → ℂ} (h : Meromorphic f)
    (h₂ : 0 < meromorphicOrderAt f 0) :
    circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 = 0 := by
  simpa using
    Real.circleAverage_const_on_circle
      (f := fun a : ℂ => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖)
      (c := (0 : ℂ)) (R := (1 : ℝ)) (a := (0 : ℝ))
      (log_trailingCoeff_eq_zero_on_unitSphere h h₂)

/-- If `f` has a pole at the origin, subtracting a nonzero constant does not change the trailing
coefficient at `0`. -/
private lemma meromorphicTrailingCoeff_sub_const_eq_of_meromorphicOrderAt_neg {f : ℂ → ℂ}
    (_ : Meromorphic f) (hneg : meromorphicOrderAt f 0 < 0) {a : ℂ} (ha : a ≠ 0) :
    meromorphicTrailingCoeffAt (f · - a) 0 = meromorphicTrailingCoeffAt f 0 := by
  have hconst : MeromorphicAt (fun _ ↦ -a : ℂ → ℂ) 0 := analyticAt_const.meromorphicAt
  have h_order_const : meromorphicOrderAt (fun _ ↦ -a : ℂ → ℂ) 0 = 0 := by
    simp [meromorphicOrderAt_const, ha]
  have h_lt : meromorphicOrderAt f 0 < meromorphicOrderAt (fun _ ↦ -a : ℂ → ℂ) 0 := by
    simpa [h_order_const] using hneg
  simpa [sub_eq_add_neg] using
    (MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt
      (f₁ := f) (f₂ := fun _ ↦ -a) (x := 0) (hf₂ := hconst) h_lt)

/-- If `f` has meromorphic order `0` at the origin and the leading terms do not cancel, then
subtracting `a` subtracts `a` from the trailing coefficient at `0`. -/
private lemma meromorphicTrailingCoeff_sub_const_eq_sub_of_meromorphicOrderAt_eq_zero {f : ℂ → ℂ}
    (h : Meromorphic f) (hzero : meromorphicOrderAt f 0 = 0)
    {a : ℂ} (ha0 : a ≠ 0) (ha : meromorphicTrailingCoeffAt f 0 ≠ a) :
    meromorphicTrailingCoeffAt (f · - a) 0 = meromorphicTrailingCoeffAt f 0 - a := by
  have hmero : MeromorphicAt f 0 := h 0
  have hconst : MeromorphicAt (fun _ ↦ -a : ℂ → ℂ) 0 := analyticAt_const.meromorphicAt
  have h_order_const : meromorphicOrderAt (fun _ ↦ -a : ℂ → ℂ) 0 = 0 := by
    simp [meromorphicOrderAt_const, ha0]
  have h_noncancel :
      meromorphicTrailingCoeffAt f 0 + meromorphicTrailingCoeffAt (fun _ ↦ -a : ℂ → ℂ) 0 ≠ 0 := by
    simpa [sub_eq_add_neg, meromorphicTrailingCoeffAt_const] using sub_ne_zero.mpr ha
  simpa [sub_eq_add_neg, meromorphicTrailingCoeffAt_const] using
    (MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add
      (f₁ := f) (f₂ := fun _ ↦ -a) (x := 0) hmero hconst
      (by simpa [h_order_const] using hzero) h_noncancel)

private lemma singleton_compl_mem_codiscreteWithin_unitSphere (z : ℂ) :
    {a : ℂ | z ≠ a} ∈ codiscreteWithin (Metric.sphere (0 : ℂ) |(1 : ℝ)|) := by
  apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
  intro a ha
  refine ⟨Set.univ, by simp, ?_⟩
  apply Set.Subsingleton.finite
  intro a₁ ha₁ a₂ ha₂
  simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_diff, Set.mem_setOf_eq,
    Decidable.not_not] at ha₁ ha₂
  calc
    a₁ = z := ha₁.2.symm
    _ = a₂ := ha₂.2

private lemma eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero {f : ℂ → ℂ}
    (h : Meromorphic f) (hzero : meromorphicOrderAt f 0 = 0) :
    (fun a ↦ log ‖meromorphicTrailingCoeffAt f 0 - a‖) =ᶠ[
      codiscreteWithin (Metric.sphere (0 : ℂ) |(1 : ℝ)|)]
      (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) := by
  filter_upwards
      [self_mem_codiscreteWithin (Metric.sphere (0 : ℂ) |(1 : ℝ)|),
        singleton_compl_mem_codiscreteWithin_unitSphere (meromorphicTrailingCoeffAt f 0)]
      with a ha_sphere ha_ne
  have h_tc := meromorphicTrailingCoeff_sub_const_eq_sub_of_meromorphicOrderAt_eq_zero h hzero
    (ne_zero_of_mem_unitSphere ha_sphere) ha_ne
  simp [h_tc]

private lemma log_trailingCoeff_eq_const_on_unitSphere_of_meromorphicOrderAt_neg {f : ℂ → ℂ}
    (h : Meromorphic f) (hneg : meromorphicOrderAt f 0 < 0) :
    ∀ a ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|,
      log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ =
        log ‖meromorphicTrailingCoeffAt f 0‖ := by
  intro a ha
  simp [meromorphicTrailingCoeff_sub_const_eq_of_meromorphicOrderAt_neg h hneg
    (ne_zero_of_mem_unitSphere ha)]

/-- If `f` has a pole at the origin, then the Cartan trailing-coefficient correction term is circle
integrable in the value variable. -/
private lemma circleIntegrable_log_trailingCoeff_of_meromorphicOrderAt_neg {f : ℂ → ℂ}
    (h : Meromorphic f) (hneg : meromorphicOrderAt f 0 < 0) :
    CircleIntegrable
      (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  apply circleIntegrable_of_const_on_sphere (C := log ‖meromorphicTrailingCoeffAt f 0‖)
  exact log_trailingCoeff_eq_const_on_unitSphere_of_meromorphicOrderAt_neg h hneg

/-- If `f` has meromorphic order `0` at the origin, then the Cartan trailing-coefficient
correction term is circle integrable in the value variable. -/
private lemma circleIntegrable_log_trailingCoeff_of_meromorphicOrderAt_eq_zero {f : ℂ → ℂ}
    (h : Meromorphic f) (hzero : meromorphicOrderAt f 0 = 0) :
    CircleIntegrable
      (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  exact CircleIntegrable.congr_codiscreteWithin
    (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero h hzero)
    (circleIntegrable_log_norm_sub (meromorphicTrailingCoeffAt f 0) 0 1)

/-- If `f` has a zero at the origin, then the Cartan trailing-coefficient correction term is circle
integrable in the value variable. -/
private lemma circleIntegrable_log_trailingCoeff {f : ℂ → ℂ} (h : Meromorphic f)
    (h₂ : 0 < meromorphicOrderAt f 0) :
    CircleIntegrable
      (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  apply circleIntegrable_of_const_on_sphere (C := 0)
  exact log_trailingCoeff_eq_zero_on_unitSphere h h₂

/-- Auxiliary integrability statement for the trailing-coefficient term in Cartan's formula. -/
lemma circleIntegrable_log_trailingCoeff_of_meromorphic {f : ℂ → ℂ} (h : Meromorphic f) :
    CircleIntegrable
      (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  rcases lt_trichotomy (meromorphicOrderAt f 0) 0 with hneg | hzero | hpos
  · exact circleIntegrable_log_trailingCoeff_of_meromorphicOrderAt_neg h hneg
  · exact circleIntegrable_log_trailingCoeff_of_meromorphicOrderAt_eq_zero h hzero
  · exact circleIntegrable_log_trailingCoeff h hpos

end Cartan
end ValueDistribution
