/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.SMT.DivisorDeriv
import VD.SMT.ProximityEstimates

/-!
# The Second Main Theorem with Ramification Term — SMT work package E

See `VD/SMT/PLAN-SecondMainTheorem.md`, §7.

Mathlib target: `Mathlib/Analysis/Complex/ValueDistribution/SecondMainTheorem.lean`
(part 2 of 3).
Dependencies: `VD/SMT/DivisorDeriv.lean` (package B) and
`VD/SMT/ProximityEstimates.lean` (package D).

This file proves the **Second Main Theorem** of value distribution theory in Lang's form,
with the ramification term: for `f` meromorphic on `ℂ` and finitely many distinct finite
targets `a₁, …, a_q`,

```
m(r, ∞) + Σⱼ m(r, aⱼ) + N₁(r)  ≤  2 T(r, f)  +  O(log⁺ T(r, f) + log r),
N₁(r) = N(r, 1/f′) + 2 N(r, f) − N(r, f′)
```

as `r → ∞` outside a set of finite Lebesgue measure. The result carries **no**
nondegeneracy hypothesis on `f`: the degenerate case, where `deriv f` vanishes to
infinite order, is handled through the constancy dichotomy of work package D.

## Main results

- `ValueDistribution.secondMainTheorem_ramification`: the Second Main Theorem with
  ramification term (S1).
- `ValueDistribution.secondMainTheorem_ramification_posPart`: the `posPart`
  reformulation (S1′), a filter-algebra-composable `IsBigO` statement.
- `ValueDistribution.ramification_nonneg`: the ramification term `N₁` is nonnegative, so
  users may simply drop it from the estimate.

References: [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677], Theorem
VII.2.1; [Hayman, *Meromorphic Functions*][MR164038], §2.1.
-/

open Asymptotics Filter MeasureTheory Metric Real Set Topology

namespace ValueDistribution

/-!
## Nonnegativity of the Ramification Term
-/

/--
The ramification term `N₁(r) = N(r, 1/f′) + 2 N(r, f) − N(r, f′)` of the Second Main
Theorem is nonnegative for `1 ≤ r`.
-/
theorem ramification_nonneg {f : ℂ → ℂ} (hf : Meromorphic f) {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ logCounting (deriv f) 0 r + 2 * logCounting f ⊤ r - logCounting (deriv f) ⊤ r := by
  -- By the pole-divisor formula of package B, the term equals
  -- `N(r, 1/f′) + N(r, f) − N̄(r, f)`, a sum of nonnegative quantities.
  have h₁ : logCounting (deriv f) ⊤ r = logCounting f ⊤ r + truncatedLogCounting f ⊤ r := by
    rw [logCounting_deriv_top hf]
    rfl
  have h₂ : truncatedLogCounting f ⊤ r ≤ logCounting f ⊤ r := truncatedLogCounting_le hr
  have h₃ : 0 ≤ logCounting (deriv f) 0 r := logCounting_nonneg hr
  linarith

/-!
## The Second Main Theorem
-/

/--
**Second Main Theorem** of value distribution theory, with ramification term (Lang's
form): if `f` is meromorphic on `ℂ` and `s` is a finite set of finite targets, then

`m(r, ∞) + Σₐ m(r, a) + N₁(r) ≤ 2 T(r, f) + c (log⁺ T(r, f) + log r)`

for all sufficiently large `r` outside a set of finite Lebesgue measure, where
`N₁(r) = N(r, 1/f′) + 2 N(r, f) − N(r, f′)` is the (nonnegative) ramification term. No
nondegeneracy hypothesis on `f` is needed.
-/
theorem secondMainTheorem_ramification {f : ℂ → ℂ} (hf : Meromorphic f) (s : Finset ℂ) :
    ∃ c, ∀ᶠ r in volume.cofinite ⊓ atTop,
      proximity f ⊤ r + ∑ a ∈ s, proximity f a r
        + (logCounting (deriv f) 0 r + 2 * logCounting f ⊤ r - logCounting (deriv f) ⊤ r)
      ≤ 2 * characteristic f ⊤ r + c * (log⁺ (characteristic f ⊤ r) + Real.log r) := by
  have hd : Meromorphic (deriv f) := hf.deriv
  by_cases h' : ∀ x, meromorphicOrderAt (deriv f) x ≠ ⊤
  -- **Main case**: the order of `deriv f` is finite everywhere.
  · have h'f : ∀ x, meromorphicOrderAt f x ≠ ⊤ :=
      fun x hx ↦ h' x (meromorphicOrderAt_deriv_eq_top hx)
    -- The integrated separation bound (D4) …
    obtain ⟨c₂, hc₂⟩ := sum_proximity_le hf h' s
    -- … and one uniform constant for the Lemma on the Logarithmic Derivative applied to
    -- `f` itself and to all shifted targets (D2).
    obtain ⟨C₀, hC₀⟩ := isBigO_iff.1 <| (isBigO_proximity_logDeriv hf).add
      (IsBigO.sum fun a (_ : a ∈ s) ↦ isBigO_proximity_logDeriv_shift hf a)
    set c₁ := max |Real.log ‖deriv f 0‖| |Real.log ‖meromorphicTrailingCoeffAt (deriv f) 0‖|
      with hc₁def
    refine ⟨C₀ + c₁ + max c₂ 0, ?_⟩
    filter_upwards [hC₀, mem_inf_of_right (eventually_ge_atTop (Real.exp 1))] with r hbound hre
    have hr1 : (1 : ℝ) ≤ r := by linarith [Real.add_one_le_exp 1]
    have hr0 : r ≠ 0 := (one_pos.trans_le hr1).ne'
    have hlogr : 1 ≤ Real.log r := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hre
    have hv1 : 1 ≤ log⁺ (characteristic f ⊤ r) + Real.log r := by
      linarith [posLog_nonneg (x := characteristic f ⊤ r)]
    -- First Main Theorem, part 1, for `deriv f`:
    -- `m(r, 1/f′) + N(r, 1/f′) ≤ m(r, f′) + N(r, f′) + c₁`
    have hfmt : proximity (deriv f)⁻¹ ⊤ r + logCounting (deriv f) 0 r
        ≤ proximity (deriv f) ⊤ r + logCounting (deriv f) ⊤ r + c₁ := by
      have h₁ := characteristic_sub_characteristic_inv_le (R := r) hd
      rw [abs_le] at h₁
      have h₂ := h₁.1
      unfold characteristic at h₂
      simp only [Pi.add_apply, logCounting_inv] at h₂
      linarith
    -- D3: `m(r, f′) ≤ m(r, f) + m(r, f′/f)`
    have hd3 : proximity (deriv f) ⊤ r ≤ proximity f ⊤ r + proximity (logDeriv f) ⊤ r :=
      proximity_deriv_top_le hf h'f hr0
    -- D4 at radius `r`
    have hd4 := hc₂ r hr1
    -- LLD and D2: the logarithmic-derivative proximity terms are error terms.
    have hS : proximity (logDeriv f) ⊤ r + ∑ a ∈ s, proximity (logDeriv (f · - a)) ⊤ r
        ≤ C₀ * (log⁺ (characteristic f ⊤ r) + Real.log r) := by
      calc proximity (logDeriv f) ⊤ r + ∑ a ∈ s, proximity (logDeriv (f · - a)) ⊤ r
          ≤ ‖proximity (logDeriv f) ⊤ r + ∑ a ∈ s, proximity (logDeriv (f · - a)) ⊤ r‖ :=
            le_abs_self _
        _ ≤ C₀ * ‖log⁺ (characteristic f ⊤ r) + Real.log r‖ := hbound
        _ = C₀ * (log⁺ (characteristic f ⊤ r) + Real.log r) := by
            rw [Real.norm_of_nonneg (by linarith)]
    -- Absorb the additive constants `c₁` and `c₂` into the error term.
    have hc1 : (0 : ℝ) ≤ c₁ := le_trans (abs_nonneg _) (le_max_left _ _)
    have habs₁ : c₁ * 1 ≤ c₁ * (log⁺ (characteristic f ⊤ r) + Real.log r) :=
      mul_le_mul_of_nonneg_left hv1 hc1
    have habs₂ : c₂ ≤ max c₂ 0 * (log⁺ (characteristic f ⊤ r) + Real.log r) :=
      calc c₂ ≤ max c₂ 0 * 1 := by rw [mul_one]; exact le_max_left _ _
        _ ≤ max c₂ 0 * (log⁺ (characteristic f ⊤ r) + Real.log r) :=
            mul_le_mul_of_nonneg_left hv1 (le_max_right _ _)
    -- Assemble, using `T = m(r, ∞) + N(r, ∞)` (definitional).
    have hT : characteristic f ⊤ r = proximity f ⊤ r + logCounting f ⊤ r := rfl
    nlinarith [hfmt, hd3, hd4, hS, habs₁, habs₂, hT]
  -- **Degenerate case**: `deriv f` vanishes to infinite order somewhere; then `f` is
  -- constant away from a discrete set, and both sides of the estimate are eventually
  -- constant.
  · push Not at h'
    obtain ⟨c₀, hc₀⟩ := hf.exists_eventuallyEq_const_iff_deriv_eventuallyEq_zero.2
      ((Meromorphic.exists_meromorphicOrderAt_eq_top_iff_eventually_zero hd).1 h')
    -- The divisor of `deriv f` vanishes, and with it both of its counting functions.
    have hall : ∀ x, meromorphicOrderAt (deriv f) x = ⊤ :=
      (Meromorphic.exists_meromorphicOrderAt_eq_top_iff_forall hd).1 h'
    have hdiv : MeromorphicOn.divisor (deriv f) Set.univ = 0 := by
      ext x
      simp [MeromorphicOn.divisor_apply (meromorphicOn_univ.2 hd) (mem_univ x), hall x]
    have hN'top : logCounting (deriv f) ⊤ = 0 := by
      rw [logCounting_top, hdiv]
      simp
    have hN'zero : logCounting (deriv f) 0 = 0 := by
      rw [logCounting_zero, hdiv]
      simp
    -- The counting function of the eventually-constant function `f` vanishes as well.
    have hNf : logCounting f ⊤ = 0 := by
      rw [logCounting_congr_codiscrete hc₀, logCounting_const]
    refine ⟨log⁺ ‖c₀‖ + ∑ a ∈ s, log⁺ ‖c₀ - a‖⁻¹, ?_⟩
    filter_upwards [mem_inf_of_right (eventually_ge_atTop (Real.exp 1))] with r hre
    have hr1 : (1 : ℝ) ≤ r := by linarith [Real.add_one_le_exp 1]
    have hr0 : r ≠ 0 := (one_pos.trans_le hr1).ne'
    have hlogr : 1 ≤ Real.log r := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hre
    -- The proximity terms are eventually constant.
    have hm : proximity f ⊤ r = log⁺ ‖c₀‖ := by
      rw [proximity_congr_codiscrete hc₀ hr0, proximity_const]
    have hma : ∀ a ∈ s, proximity f ↑a r = log⁺ ‖c₀ - a‖⁻¹ := by
      intro a _
      rw [proximity_congr_codiscrete hc₀ hr0, proximity_coe]
      exact circleAverage_const _ 0 r
    have hB : 0 ≤ log⁺ ‖c₀‖ + ∑ a ∈ s, log⁺ ‖c₀ - a‖⁻¹ := by
      have h₁ : (0 : ℝ) ≤ ∑ a ∈ s, log⁺ ‖c₀ - a‖⁻¹ :=
        Finset.sum_nonneg fun a _ ↦ posLog_nonneg
      linarith [posLog_nonneg (x := ‖c₀‖)]
    rw [hm, hN'top, hN'zero, hNf, Finset.sum_congr rfl hma]
    simp only [Pi.zero_apply]
    have hv1 : 1 ≤ log⁺ (characteristic f ⊤ r) + Real.log r := by
      linarith [posLog_nonneg (x := characteristic f ⊤ r)]
    have hTnn : 0 ≤ characteristic f ⊤ r := characteristic_nonneg hr1
    linarith [mul_le_mul_of_nonneg_left hv1 hB]

/--
**Second Main Theorem**, `posPart` reformulation: the positive part of the defect of the
Second Main Theorem inequality is `O(log⁺ T(r, f) + log r)` along
`volume.cofinite ⊓ atTop`. This form composes conveniently with the filter algebra of
`Asymptotics.IsBigO`.
-/
theorem secondMainTheorem_ramification_posPart {f : ℂ → ℂ} (hf : Meromorphic f)
    (s : Finset ℂ) :
    (fun r ↦ (proximity f ⊤ r + ∑ a ∈ s, proximity f a r
        + (logCounting (deriv f) 0 r + 2 * logCounting f ⊤ r - logCounting (deriv f) ⊤ r)
        - 2 * characteristic f ⊤ r)⁺)
      =O[volume.cofinite ⊓ atTop] fun r ↦ log⁺ (characteristic f ⊤ r) + Real.log r := by
  obtain ⟨c, hc⟩ := secondMainTheorem_ramification hf s
  rw [isBigO_iff]
  refine ⟨max c 0, ?_⟩
  filter_upwards [hc, mem_inf_of_right (eventually_ge_atTop (Real.exp 1))] with r h₁ hre
  have hlogr : 1 ≤ Real.log r := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hre
  have hv0 : 0 ≤ log⁺ (characteristic f ⊤ r) + Real.log r := by
    linarith [posLog_nonneg (x := characteristic f ⊤ r)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (posPart_nonneg _),
    abs_of_nonneg hv0, posPart_def]
  apply sup_le
  · have h₂ : c * (log⁺ (characteristic f ⊤ r) + Real.log r)
        ≤ max c 0 * (log⁺ (characteristic f ⊤ r) + Real.log r) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hv0
    linarith
  · exact mul_nonneg (le_max_right _ _) hv0

/-!
## Sanity Check

For `f = Complex.exp`, both the ramification term and all counting functions vanish
identically: the exponential has no zeros and no poles, and `deriv exp = exp`. The Second
Main Theorem for `exp` is thus a statement about proximity functions alone — and it is
sharp, since `m(r, ∞) = m(r, 0) = T(r) = r / π` with defects `δ(0) = δ(∞) = 1` summing
exactly to `2`.
-/

example (r : ℝ) :
    logCounting (deriv Complex.exp) 0 r + 2 * logCounting Complex.exp ⊤ r
      - logCounting (deriv Complex.exp) ⊤ r = 0 := by
  have h₁ : MeromorphicOn.divisor Complex.exp Set.univ = 0 := by
    ext x
    have h₂ : meromorphicOrderAt Complex.exp x = 0 := by
      rw [analyticAt_cexp.meromorphicOrderAt_eq,
        analyticAt_cexp.analyticOrderAt_eq_zero.2 (Complex.exp_ne_zero x)]
      rfl
    simp [MeromorphicOn.divisor_apply
      (meromorphicOn_univ.2 fun x ↦ analyticAt_cexp.meromorphicAt) (mem_univ x), h₂]
  simp [Complex.deriv_exp, logCounting_top, logCounting_zero, h₁]

end ValueDistribution
