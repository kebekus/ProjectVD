/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Stefan Kebekus
-/

module

public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
public import Mathlib.MeasureTheory.Integral.CircleAverage

public section

open Filter Function Metric Real Set Classical Topology
open scoped Real Topology MeasureTheory Metric

variable
  {f : ℂ → ℂ}
/-!
# Cartan's Formula

This file will, in the future, establish Cartan's classic formula, describing
the characteristic function `characteristic f ⊤ r` as a sum of two circle
averages, `circleAverage (logCounting f · r) 0 1` and `circleAverage (fun a ↦
Real.log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1`.  As a corollary, it
implies the (surprising non-trival) fact that the characteristic function is
monotone.



isolates the trailing-coefficient terms that appear before the final averaging
step in Cartan's formula.

## Main statements

- `ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_log_trailingCoeff`
- `ValueDistribution.Cartan.logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top`
- `ValueDistribution.Cartan.circleAverage_log_trailingCoeff_eq_zero`

## Implementation notes

The root theorem is a Jensen / First Main Theorem reformulation. The auxiliary
lemmas in `ValueDistribution.Cartan` specialize that identity to `f - a` and
analyze the corresponding trailing-coefficient averages that appear in
`VD/Cartan.lean`.

## References

* [S. Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677]

## Tags

Cartan, Nevanlinna theory, trailing coefficient, log counting
-/


variable
   {𝕜 : Type*} [NontriviallyNormedField 𝕜]
   {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
# Material for meromorphicTrailingCoeffAt
-/

/--
In case where `g : ℂ → ℂ` is meromorphic of order zero at `x`, express the
trailing coefficient as a limit.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_eq_of_tendsto_order_eq_zero {g : 𝕜 → E} {x : 𝕜} {e : E}
    (h₁g : MeromorphicAt g x) (h₂g : meromorphicOrderAt g x = 0)
    (h₃g : Tendsto g (𝓝[≠] x) (𝓝 e)) :
    meromorphicTrailingCoeffAt g x = e :=
  tendsto_nhds_unique (by simpa [h₂g] using h₁g.tendsto_nhds_meromorphicTrailingCoeffAt) h₃g


namespace ValueDistribution


namespace Cartan

/--
If `f` has a zero at the origin, then subtracting a nonzero constant shifts the
trailing coefficient of `f` at `0` to that constant term.
-/
private lemma meromorphicTrailingCoeff_sub_const_eq_neg
    (h : Meromorphic f) (h₂ : 0 < meromorphicOrderAt f 0) {a : ℂ} (ha : a ≠ 0) :
    meromorphicTrailingCoeffAt (f · - a) 0 = -a := by
  let g : ℂ → ℂ := (f · - a)
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
    hmero_g.meromorphicTrailingCoeffAt_eq_of_tendsto_order_eq_zero h_ord h_tendsto_g

private lemma log_trailingCoeff_eq_zero_on_unitSphere
    (h : Meromorphic f) (h₂ : 0 < meromorphicOrderAt f 0) :
    ∀ a ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|,
      log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ = (0 : ℝ) := by
  intro a ha
  rw [meromorphicTrailingCoeff_sub_const_eq_neg h h₂ (by aesop)]
  aesop

/-- If `f` has a zero at the origin, then the trailing-coefficient correction term vanishes after
averaging over the unit circle. -/
lemma circleAverage_log_trailingCoeff_eq_zero (h : Meromorphic f)
    (h₂ : 0 < meromorphicOrderAt f 0) :
    circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 = 0 := by
  simpa using
    Real.circleAverage_const_on_circle
      (f := fun a : ℂ => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖)
      (c := (0 : ℂ)) (R := (1 : ℝ)) (a := (0 : ℝ))
      (log_trailingCoeff_eq_zero_on_unitSphere h h₂)

/-- If `f` has a pole at the origin, subtracting a nonzero constant does not change the trailing
coefficient at `0`. -/
private lemma meromorphicTrailingCoeff_sub_const_eq_of_meromorphicOrderAt_neg
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

/- If `f` has meromorphic order `0` at the origin and the leading terms do not cancel, then
subtracting `a` subtracts `a` from the trailing coefficient at `0`. -/
private lemma meromorphicTrailingCoeff_sub_const_eq_sub_of_meromorphicOrderAt_eq_zero
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

private lemma eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero
    (h : Meromorphic f) (hzero : meromorphicOrderAt f 0 = 0) :
    (log ‖meromorphicTrailingCoeffAt f 0 - ·‖) =ᶠ[
      codiscreteWithin (Metric.sphere (0 : ℂ) |(1 : ℝ)|)]
      (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) := by
  filter_upwards
      [self_mem_codiscreteWithin (Metric.sphere (0 : ℂ) |(1 : ℝ)|),
        singleton_compl_mem_codiscreteWithin_unitSphere (meromorphicTrailingCoeffAt f 0)]
      with a ha_sphere ha_ne
  rw [meromorphicTrailingCoeff_sub_const_eq_sub_of_meromorphicOrderAt_eq_zero h hzero (by aesop) ha_ne]

/-- Auxiliary integrability statement for the trailing-coefficient term in Cartan's formula. -/
theorem circleIntegrable_log_trailingCoeff_of_meromorphic (h : Meromorphic f) :
    CircleIntegrable (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  rcases lt_trichotomy (meromorphicOrderAt f 0) 0 with hneg | hzero | hpos
  · apply (circleIntegrable_congr _).2 (circleIntegrable_const (log ‖meromorphicTrailingCoeffAt f 0‖) 0 1)
    intro a ha
    simp only
    rw [meromorphicTrailingCoeff_sub_const_eq_of_meromorphicOrderAt_neg h hneg (by aesop)]
  · apply CircleIntegrable.congr_codiscreteWithin
     (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero h hzero)
    convert circleIntegrable_log_norm_sub_const (a := meromorphicTrailingCoeffAt f 0) (c := 0) 1 using 1
    simp_rw [norm_sub_rev]
  · apply (circleIntegrable_congr _).2 (circleIntegrable_const 0 0 1)
    exact log_trailingCoeff_eq_zero_on_unitSphere h hpos

end Cartan
end ValueDistribution
