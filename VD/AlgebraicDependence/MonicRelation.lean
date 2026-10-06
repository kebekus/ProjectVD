/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
public import Mathlib.Analysis.Meromorphic.RCLike
public import VD.AlgebraicDependence.DivisorEstimates
public import VD.AlgebraicDependence.PointwiseEstimates
public import VD.Field.CodiscreteWithinNeBot
public import VD.LLD.LogDerivEstimates

/-!
# The Master Inequality and Algebraic Dependence — Algebraic Dependence work package C

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §5.

Mathlib target: new file `Mathlib/Analysis/Complex/ValueDistribution/AlgebraicDependence.lean`
(C0 goes to `CharacteristicFunction.lean`). Dependencies: packages A and B, and
`circleAverage_mono_codiscreteWithin` from `VD/LLD/LogDerivEstimates.lean`.

Throughout, `f : ℂ → ℂ` is meromorphic, `a : ℕ → ℂ → ℂ` is a family of meromorphic
coefficients, and `f ^ d + ∑ j ∈ range d, a j * f ^ j` is the monic polynomial expression of
degree `d` in `f` with coefficients `a j`.

## Main results

- C0, `ValueDistribution.characteristic_mul_top_le'`: `T(r, f₁ f₂) ≤ T(r, f₁) + T(r, f₂)` for
  `1 ≤ r`, without the nondegeneracy hypotheses of `characteristic_mul_top_le`.
- C1/C2, `nsmul_proximity_le_of_monic_eq`, `nsmul_logCounting_le_of_monic_eq`: the pointwise
  estimate of package A and the divisor estimate of package B, integrated.
- T1, `ValueDistribution.nsmul_characteristic_le_of_monic_eq`: the **master inequality**
  `d · T(r, f) ≤ T(r, g) + d · Σ_{j<d} T(r, a j) + d · log (2 (d + 1))` whenever
  `f ^ d + Σ_{j<d} a j * f ^ j =ᶠ[codiscrete ℂ] g`.
- T2, `ValueDistribution.characteristic_le_sum_characteristic_of_monic_eq_zero`: the
  **algebraic dependence bound** `T(r, f) ≤ Σ_{j<d} T(r, a j) + log d` for `g = 0`.
- C5, `characteristic_isBigO_of_monic_eq_zero`, `characteristic_isLittleO_of_monic_eq_zero`:
  a meromorphic function that is integral over functions of growth `O(φ)` resp. `o(φ)` has
  growth `O(φ)` resp. `o(φ)`.
-/

@[expose] public section

open Asymptotics Filter Finset Function Real Set Topology

namespace ValueDistribution

variable {f g : ℂ → ℂ} {a : ℕ → ℂ → ℂ} {d : ℕ}

/-!
## The Product Bound without Nondegeneracy Hypotheses
-/

/-- `T(r, f₁ f₂) ≤ T(r, f₁) + T(r, f₂)` for `1 ≤ r`. Variant of `characteristic_mul_top_le`
without the hypotheses `meromorphicOrderAt fᵢ z ≠ ⊤`: if one factor vanishes on a codiscrete
set, so does the product, and its characteristic is zero. -/
theorem characteristic_mul_top_le' {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r) (h₁ : Meromorphic f₁)
    (h₂ : Meromorphic f₂) :
    characteristic (f₁ * f₂) ⊤ r ≤ characteristic f₁ ⊤ r + characteristic f₂ ⊤ r := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  by_cases hf₁ : ∃ z, meromorphicOrderAt f₁ z = ⊤
  · have h0 : f₁ * f₂ =ᶠ[codiscrete ℂ] 0 := by
      filter_upwards [h₁.exists_meromorphicOrderAt_eq_top_iff_eventually_zero.1 hf₁] with z hz
      simp [hz]
    rw [characteristic_congr_codiscrete h0 hr0, characteristic_zero]
    exact add_nonneg (characteristic_nonneg hr) (characteristic_nonneg hr)
  by_cases hf₂ : ∃ z, meromorphicOrderAt f₂ z = ⊤
  · have h0 : f₁ * f₂ =ᶠ[codiscrete ℂ] 0 := by
      filter_upwards [h₂.exists_meromorphicOrderAt_eq_top_iff_eventually_zero.1 hf₂] with z hz
      simp [hz]
    rw [characteristic_congr_codiscrete h0 hr0, characteristic_zero]
    exact add_nonneg (characteristic_nonneg hr) (characteristic_nonneg hr)
  push Not at hf₁ hf₂
  exact characteristic_mul_top_le hr h₁ hf₁ h₂ hf₂

/-!
## Integration of the Pointwise and Divisor Estimates
-/

/-- The monic expression `f ^ d + Σ_{j<d} a j * f ^ j` is meromorphic. -/
theorem _root_.Meromorphic.monic (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j)) :
    Meromorphic (f ^ d + ∑ j ∈ range d, a j * f ^ j) :=
  hf.pow.add (Meromorphic.sum fun j _ ↦ (ha j).mul hf.pow)

/-- C1: the weighted root bound `Real.nsmul_posLog_norm_le_of_monic_eq`, integrated over the
circle of radius `r`. -/
theorem nsmul_proximity_le_of_monic_eq (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j))
    (r : ℝ) :
    d * proximity f ⊤ r
      ≤ proximity (f ^ d + ∑ j ∈ range d, a j * f ^ j) ⊤ r
        + d * ∑ j ∈ range d, proximity (a j) ⊤ r + d * log (2 * (d + 1)) := by
  have hint : ∀ {u : ℂ → ℂ}, Meromorphic u → CircleIntegrable (fun z ↦ log⁺ ‖u z‖) 0 r :=
    fun hu ↦ hu.meromorphicOn.circleIntegrable_posLog_norm
  have hcoef : ∀ j ∈ range d, CircleIntegrable (fun z ↦ log⁺ ‖a j z‖) 0 r :=
    fun j _ ↦ hint (ha j)
  have hF : CircleIntegrable ((d : ℝ) • fun z ↦ log⁺ ‖f z‖) 0 r :=
    IntervalIntegrable.const_mul (hint hf) _
  have hA := hint (hf.monic ha (d := d))
  have hB : CircleIntegrable ((d : ℝ) • ∑ j ∈ range d, (fun z ↦ log⁺ ‖a j z‖)) 0 r :=
    IntervalIntegrable.const_mul (CircleIntegrable.sum (range d) hcoef) _
  have hC : CircleIntegrable (fun _ : ℂ ↦ (d : ℝ) * log (2 * (d + 1))) 0 r :=
    circleIntegrable_const _ _ _
  simp only [proximity_top]
  -- The pointwise estimate, integrated.
  have key : circleAverage ((d : ℝ) • fun z ↦ log⁺ ‖f z‖) 0 r
      ≤ circleAverage ((fun z ↦ log⁺ ‖(f ^ d + ∑ j ∈ range d, a j * f ^ j) z‖)
          + (d : ℝ) • ∑ j ∈ range d, (fun z ↦ log⁺ ‖a j z‖)
          + fun _ ↦ (d : ℝ) * log (2 * (d + 1))) 0 r := by
    apply circleAverage_mono hF ((hA.add hB).add hC)
    intro z _
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    exact nsmul_posLog_norm_le_of_monic_eq (a := fun j ↦ a j z) (by simp)
  rwa [circleAverage_smul, circleAverage_add (hA.add hB) hC, circleAverage_add hA hB,
    circleAverage_smul, circleAverage_sum hcoef, circleAverage_const, smul_eq_mul,
    smul_eq_mul] at key

/-- C2: the divisor estimate `MeromorphicOn.nsmul_negPart_divisor_le_of_monic_eq`, at the
level of counting functions. -/
theorem nsmul_logCounting_le_of_monic_eq (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j))
    {r : ℝ} (hr : 1 ≤ r) :
    d * logCounting f ⊤ r
      ≤ logCounting (f ^ d + ∑ j ∈ range d, a j * f ^ j) ⊤ r
        + d * ∑ j ∈ range d, logCounting (a j) ⊤ r := by
  simp only [logCounting_top]
  have := locallyFinsuppWithin.logCounting_le
    (hf.meromorphicOn.nsmul_negPart_divisor_le_of_monic_eq (d := d) fun j ↦ (ha j).meromorphicOn) hr
  simpa [Finset.sum_apply, nsmul_eq_mul] using this

/-!
## The Master Inequality and the Algebraic Dependence Bound
-/

/-- **The master inequality** (T1): if `f ^ d + Σ_{j<d} a j * f ^ j = g` away from a discrete
set, then `d · T(r, f) ≤ T(r, g) + d · Σ_{j<d} T(r, a j) + d · log (2 (d + 1))` for `1 ≤ r`.
The factor `d` on the left is the source of the factor `deg P` in the Valiron–Mohon'ko
identity. -/
theorem nsmul_characteristic_le_of_monic_eq (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j))
    (h : f ^ d + ∑ j ∈ range d, a j * f ^ j =ᶠ[codiscrete ℂ] g) {r : ℝ} (hr : 1 ≤ r) :
    d * characteristic f ⊤ r
      ≤ characteristic g ⊤ r + d * ∑ j ∈ range d, characteristic (a j) ⊤ r
        + d * log (2 * (d + 1)) := by
  rw [← characteristic_congr_codiscrete h (zero_lt_one.trans_le hr).ne']
  simp only [characteristic, Pi.add_apply, Finset.sum_add_distrib]
  linarith [nsmul_proximity_le_of_monic_eq (d := d) hf ha r,
    nsmul_logCounting_le_of_monic_eq (d := d) hf ha hr]

/-- **The algebraic dependence bound** (T2): if `f ^ d + Σ_{j<d} a j * f ^ j = 0` away from a
discrete set, then `T(r, f) ≤ Σ_{j<d} T(r, a j) + log d` for `1 ≤ r`. In particular, a
meromorphic function that is integral over a family of meromorphic functions grows no faster
than the sum of their characteristics. -/
theorem characteristic_le_sum_characteristic_of_monic_eq_zero (hf : Meromorphic f)
    (ha : ∀ j, Meromorphic (a j)) (h : f ^ d + ∑ j ∈ range d, a j * f ^ j =ᶠ[codiscrete ℂ] 0)
    {r : ℝ} (hr : 1 ≤ r) :
    characteristic f ⊤ r ≤ ∑ j ∈ range d, characteristic (a j) ⊤ r + log d := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  -- The degree is positive: for `d = 0` the hypothesis says `1 = 0` on a nonempty set.
  have hd : (0 : ℝ) < d := by
    rcases d with _ | d
    · have : (codiscrete ℂ).NeBot :=
        isPreconnected_univ.codiscreteWithin_neBot Set.nontrivial_univ
      obtain ⟨z, hz⟩ := h.exists
      simp at hz
    · positivity
  simp only [characteristic, Pi.add_apply, Finset.sum_add_distrib]
  -- The proximity part: the unweighted root bound, integrated where the relation holds.
  have hm : proximity f ⊤ r ≤ ∑ j ∈ range d, proximity (a j) ⊤ r + log d := by
    have hint : ∀ {u : ℂ → ℂ}, Meromorphic u → CircleIntegrable (fun z ↦ log⁺ ‖u z‖) 0 r :=
      fun hu ↦ hu.meromorphicOn.circleIntegrable_posLog_norm
    have hcoef : ∀ j ∈ range d, CircleIntegrable (fun z ↦ log⁺ ‖a j z‖) 0 r :=
      fun j _ ↦ hint (ha j)
    have hB := CircleIntegrable.sum (range d) hcoef
    have hC : CircleIntegrable (fun _ : ℂ ↦ log (d : ℝ)) 0 r := circleIntegrable_const _ _ _
    simp only [proximity_top]
    have key : circleAverage (fun z ↦ log⁺ ‖f z‖) 0 r
        ≤ circleAverage (∑ j ∈ range d, (fun z ↦ log⁺ ‖a j z‖) + fun _ ↦ log (d : ℝ)) 0 r := by
      apply circleAverage_mono_codiscreteWithin hr0 (hint hf) (hB.add hC)
      filter_upwards [h.filter_mono (codiscreteWithin_mono (subset_univ _))] with z hz
      simp only [Pi.add_apply, Finset.sum_apply]
      exact posLog_norm_le_of_monic_eq_zero (a := fun j ↦ a j z)
        (by simpa [Finset.sum_apply] using hz)
    rwa [circleAverage_add hB hC, circleAverage_sum hcoef, circleAverage_const] at key
  -- The counting part: the divisor estimate, with the relation's divisor being zero.
  have hN : logCounting f ⊤ r ≤ ∑ j ∈ range d, logCounting (a j) ⊤ r := by
    have h0 : logCounting (0 : ℂ → ℂ) ⊤ r = 0 := by
      have h₁ : proximity (0 : ℂ → ℂ) ⊤ r + logCounting (0 : ℂ → ℂ) ⊤ r = 0 :=
        congrFun characteristic_zero r
      have h₂ : 0 ≤ proximity (0 : ℂ → ℂ) ⊤ r := proximity_nonneg r
      have h₃ : 0 ≤ logCounting (0 : ℂ → ℂ) ⊤ r := logCounting_nonneg hr
      linarith
    have h1 := nsmul_logCounting_le_of_monic_eq hf ha hr (d := d)
    rw [logCounting_congr_codiscrete h, h0, zero_add] at h1
    exact (mul_le_mul_iff_of_pos_left hd).1 h1
  linarith

/-!
## Asymptotic Corollaries
-/

/-- The bound of T2 as a big-O statement with respect to the comparison function
`Σ_{j<d} T(r, a j) + log d`, along any filter `l ≤ atTop`. -/
lemma characteristic_isBigO_sum_characteristic_add_log {l : Filter ℝ} (hl : l ≤ atTop)
    (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j))
    (h : f ^ d + ∑ j ∈ range d, a j * f ^ j =ᶠ[codiscrete ℂ] 0) :
    characteristic f ⊤ =O[l] ((∑ j ∈ range d, characteristic (a j) ⊤) + fun _ ↦ log (d : ℝ)) := by
  refine IsBigO.of_bound' ?_
  filter_upwards [hl (eventually_ge_atTop 1)] with r hr
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [Real.norm_of_nonneg (characteristic_nonneg hr), Real.norm_of_nonneg
    (add_nonneg (sum_nonneg fun j _ ↦ characteristic_nonneg hr) (log_natCast_nonneg d))]
  exact characteristic_le_sum_characteristic_of_monic_eq_zero hf ha h hr

/-- A meromorphic function that is integral over meromorphic functions of growth `O(φ)` has
growth `O(φ)`, for any comparison function `φ` dominating the constants and any filter
`l ≤ atTop`. -/
theorem characteristic_isBigO_of_monic_eq_zero {l : Filter ℝ} (hl : l ≤ atTop) {φ : ℝ → ℝ}
    (hφ : (1 : ℝ → ℝ) =O[l] φ) (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j))
    (ha' : ∀ j ∈ range d, characteristic (a j) ⊤ =O[l] φ)
    (h : f ^ d + ∑ j ∈ range d, a j * f ^ j =ᶠ[codiscrete ℂ] 0) :
    characteristic f ⊤ =O[l] φ :=
  (characteristic_isBigO_sum_characteristic_add_log hl hf ha h).trans
    ((IsBigO.sum ha').add ((isBigO_const_const (log (d : ℝ)) one_ne_zero l).trans hφ))

/-- A meromorphic function that is integral over meromorphic functions of growth `o(φ)` has
growth `o(φ)`, for any comparison function `φ` tending to infinity and any filter `l ≤ atTop`.
With `φ = T(r, f₀)` for a nonconstant `f₀` and `l = volume.cofinite ⊓ atTop`, this says that
functions algebraic over the field of small functions `S(f₀)` are small. -/
theorem characteristic_isLittleO_of_monic_eq_zero {l : Filter ℝ} (hl : l ≤ atTop) {φ : ℝ → ℝ}
    (hφ : Tendsto φ l atTop) (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j))
    (ha' : ∀ j ∈ range d, characteristic (a j) ⊤ =o[l] φ)
    (h : f ^ d + ∑ j ∈ range d, a j * f ^ j =ᶠ[codiscrete ℂ] 0) :
    characteristic f ⊤ =o[l] φ := by
  refine (characteristic_isBigO_sum_characteristic_add_log hl hf ha h).trans_isLittleO
    ((IsLittleO.sum ha').add (isLittleO_const_left.2 (Or.inr ?_)))
  simpa [Function.comp_def, Real.norm_eq_abs] using tendsto_abs_atTop_atTop.comp hφ

end ValueDistribution
