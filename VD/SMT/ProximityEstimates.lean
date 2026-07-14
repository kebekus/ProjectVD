/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.LLD.LogDerivLemma
import VD.MathlibPending.CharacteristicMoebius
import VD.MathlibSubmitted.MeromorphicLogDeriv
import VD.SMT.SeparationLemma

/-!
# Proximity Estimates for the Second Main Theorem — SMT work package D

See `VD/SMT/PLAN-SecondMainTheorem.md`, §6.

Mathlib target: `Mathlib/Analysis/Complex/ValueDistribution/SecondMainTheorem.lean`
(part 1 of 3).
Dependencies: `VD/SMT/SeparationLemma.lean` (package C), the Lemma on the Logarithmic
Derivative (`VD/LLD/LogDerivLemma.lean`), and the pending
`VD/MathlibPending/CharacteristicMoebius.lean` (D1 only).

This file collects the four proximity estimates from which the Second Main Theorem of
value distribution theory is assembled:

- D1, `Meromorphic.eventuallyEq_const_of_exists_meromorphicOrderAt_deriv_eq_top`: the
  constancy dichotomy — a meromorphic function on `ℂ` whose derivative vanishes somewhere
  to infinite order is constant away from a discrete set. This isolates the degenerate
  case of the hypothesis-free Second Main Theorem.

- D2, `ValueDistribution.isBigO_proximity_logDeriv_shift`: `m(r, f′/(f − a)) = S(r)` —
  the Lemma on the Logarithmic Derivative for `f - a`, with the error expressed through
  the characteristic of `f` itself (via the First Main Theorem, shift invariance).

- D3, `ValueDistribution.proximity_deriv_top_le`: `m(r, f′) ≤ m(r, f) + m(r, f′/f)`.

- D4, `ValueDistribution.sum_proximity_le`: the integrated separation bound
  `Σₐ m(r, a) ≤ m(r, 1/f′) + Σₐ m(r, f′/(f − a)) + c`, obtained by applying the
  separation lemma pointwise on circles and comparing circle averages.

The junk-value discipline follows the Lemma on the Logarithmic Derivative: all function
identities are asserted only up to equality away from codiscrete sets and consumed through
`proximity_congr_codiscrete`.

References: [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677], Ch. VII, §2;
[Hayman, *Meromorphic Functions*][MR164038], §2.1.
-/

open Asymptotics Filter MeasureTheory Metric Real Set Topology ValueDistribution

/-!
## Congruence Lemma for Derivatives

Like the logarithmic derivative (`logDeriv_congr_codiscreteWithin`), the derivative on an
open set `U` only depends on the equivalence class of the function with respect to
equality away from codiscrete subsets of `U`. This is pure calculus and requires no
meromorphy assumption.
-/

/--
If two functions agree on a codiscrete subset of an open set `U`, then so do their
derivatives.
-/
theorem deriv_congr_codiscreteWithin {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : 𝕜 → E} {U : Set 𝕜}
    (hU : IsOpen U) (h : f =ᶠ[codiscreteWithin U] g) :
    deriv f =ᶠ[codiscreteWithin U] deriv g := by
  filter_upwards [h, self_mem_codiscreteWithin U] with y h₁y h₂y
  have h₃y : f =ᶠ[𝓝 y] g := by
    have h₄ : {z | f z = g z} ∪ Uᶜ ∈ 𝓝 y := by
      rw [← nhdsNE_sup_pure y, mem_sup]
      exact ⟨mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h y h₂y,
        mem_pure.2 (mem_union_left _ h₁y)⟩
    filter_upwards [h₄, hU.mem_nhds h₂y] with z h₁z h₂z
    rcases h₁z with h₁z | h₁z
    · exact h₁z
    · exact absurd h₂z h₁z
  exact h₃y.deriv_eq

/-!
## D1: The Constancy Dichotomy

The degenerate case of the Second Main Theorem: if the derivative of a meromorphic
function vanishes to infinite order at a single point, then the function is constant away
from a discrete set. This allows stating the Second Main Theorem without any
nondegeneracy hypothesis.
-/

/--
A meromorphic function on `ℂ` whose derivative vanishes somewhere to infinite order is
constant away from a discrete set.
-/
theorem Meromorphic.eventuallyEq_const_of_exists_meromorphicOrderAt_deriv_eq_top
    {f : ℂ → ℂ} (hf : Meromorphic f) (h : ∃ x, meromorphicOrderAt (deriv f) x = ⊤) :
    ∃ c, f =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  have hd : Meromorphic (deriv f) := hf.deriv
  -- The derivative vanishes to infinite order everywhere, so the meromorphic order of
  -- `f` at every point is `0` or `⊤`.
  have h' : ∀ x, meromorphicOrderAt (deriv f) x = ⊤ :=
    hd.exists_meromorphicOrderAt_eq_top_iff_forall.1 h
  have horder : ∀ x, meromorphicOrderAt f x = 0 ∨ meromorphicOrderAt f x = ⊤ := by
    intro x
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hcon.2
    have hn0 : n ≠ 0 := fun h0 ↦ hcon.1 (by simp [← hn, h0])
    have := meromorphicOrderAt_deriv_eq_sub_one
      ((Int.cast_ne_zero (α := ℂ)).2 hn0) hn.symm
    rw [h' x] at this
    exact WithTop.coe_ne_top this.symm
  by_cases htop : ∃ x, meromorphicOrderAt f x = ⊤
  -- If `f` itself vanishes to infinite order somewhere, it vanishes away from a
  -- discrete set, and the constant is `0`.
  · exact ⟨0, hf.exists_meromorphicOrderAt_eq_top_iff_eventually_zero.1 htop⟩
  -- Otherwise, the order of `f` is `0` everywhere; pass to the normal form `g`, which is
  -- then analytic on all of `ℂ`.
  push Not at htop
  have h0 : ∀ x, meromorphicOrderAt f x = 0 := fun x ↦ (horder x).resolve_right (htop x)
  have hfU : MeromorphicOn f Set.univ := meromorphicOn_univ.2 hf
  set g := toMeromorphicNFOn f Set.univ with hg_def
  have hfg : f =ᶠ[codiscrete ℂ] g := toMeromorphicNFOn_eqOn_codiscrete hfU
  have hg : ∀ x, AnalyticAt ℂ g x := by
    intro x
    have h₁ : MeromorphicNFAt g x := meromorphicNFOn_toMeromorphicNFOn f Set.univ (mem_univ x)
    rw [← h₁.meromorphicOrderAt_nonneg_iff_analyticAt,
      meromorphicOrderAt_toMeromorphicNFOn hfU (mem_univ x), h0 x]
  -- The derivative of `g` vanishes on a codiscrete set, hence everywhere by the identity
  -- theorem …
  have h₂ : deriv g =ᶠ[codiscrete ℂ] 0 :=
    (deriv_congr_codiscreteWithin isOpen_univ hfg).symm.trans
      (hd.exists_meromorphicOrderAt_eq_top_iff_eventually_zero.1 h)
  have h₃ : ∀ x, deriv g x = 0 := by
    have h₄ : ∃ᶠ z in 𝓝[≠] (0 : ℂ), deriv g z = 0 :=
      Filter.Eventually.frequently (mem_codiscrete_iff_forall_mem_nhdsNE.1 h₂ 0)
    exact fun x ↦ AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (fun x _ ↦ (hg x).deriv) isPreconnected_univ (mem_univ 0) h₄ (mem_univ x)
  -- … so `g` is constant, and `f` agrees with it away from a discrete set.
  have h₄ : ∀ x, g x = g 0 :=
    fun x ↦ is_const_of_deriv_eq_zero (fun x ↦ (hg x).differentiableAt) h₃ x 0
  exact ⟨g 0, hfg.trans (Eventually.of_forall h₄)⟩

namespace ValueDistribution

/-!
## D2: The Lemma on the Logarithmic Derivative for Shifted Targets
-/

/--
**Lemma on the Logarithmic Derivative, arbitrary finite targets**: for `f` meromorphic on
the complex plane and any value `a`, the proximity function of `logDeriv (f · - a)` for
the value `⊤` satisfies `m(r, f′/(f - a)) = O(log⁺ T(r, f) + log r)` as `r → ∞`, outside
an exceptional set of finite Lebesgue measure. Note that the error is expressed through
the characteristic of `f` itself, not that of `f - a`.
-/
theorem isBigO_proximity_logDeriv_shift {f : ℂ → ℂ} (hf : Meromorphic f) (a : ℂ) :
    proximity (logDeriv (f · - a)) ⊤ =O[volume.cofinite ⊓ atTop]
      fun r ↦ log⁺ (characteristic f ⊤ r) + Real.log r := by
  have hfa : Meromorphic (f · - a) := by fun_prop
  -- The Lemma on the Logarithmic Derivative for `f - a`, with the error expressed
  -- through the characteristic of `f - a` …
  refine (isBigO_proximity_logDeriv hfa).trans ?_
  -- … whose comparison function is dominated by that of `f`, by the First Main Theorem.
  rw [isBigO_iff]
  refine ⟨1 + (Real.log 2 + log⁺ (log⁺ ‖a‖ + Real.log 2)), ?_⟩
  filter_upwards [mem_inf_of_right (eventually_ge_atTop (Real.exp 1))] with r hre
  have hr1 : (1 : ℝ) ≤ r := by linarith [Real.add_one_le_exp 1]
  have hlogr : 1 ≤ Real.log r := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hre
  -- Shift invariance of the characteristic (First Main Theorem, part 2)
  have hT : characteristic (f · - a) ⊤ r ≤ characteristic f ⊤ r + (log⁺ ‖a‖ + Real.log 2) := by
    have h₁ := abs_characteristic_sub_characteristic_shift_le (a₀ := a) (r := r) hf
    rw [abs_le] at h₁
    linarith [h₁.1]
  have h₂ : log⁺ (characteristic (f · - a) ⊤ r)
      ≤ Real.log 2 + log⁺ (characteristic f ⊤ r) + log⁺ (log⁺ ‖a‖ + Real.log 2) :=
    (posLog_le_posLog (characteristic_nonneg hr1) hT).trans posLog_add
  -- Assemble, absorbing the additive constant into the `log r` term.
  have hM : 0 ≤ Real.log 2 + log⁺ (log⁺ ‖a‖ + Real.log 2) :=
    add_nonneg (log_nonneg one_le_two) posLog_nonneg
  have h₃ := posLog_nonneg (x := characteristic f ⊤ r)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [posLog_nonneg (x := characteristic (f · - a) ⊤ r)]),
    abs_of_nonneg (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left
    (by linarith : (1 : ℝ) ≤ log⁺ (characteristic f ⊤ r) + Real.log r) hM]

/-!
## D3: Proximity of the Derivative
-/

/--
The proximity function of the derivative is bounded by that of the function plus that of
the logarithmic derivative: `m(r, f′) ≤ m(r, f) + m(r, f′/f)`.
-/
theorem proximity_deriv_top_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (h' : ∀ x, meromorphicOrderAt f x ≠ ⊤) {r : ℝ} (hr : r ≠ 0) :
    proximity (deriv f) ⊤ r ≤ proximity f ⊤ r + proximity (logDeriv f) ⊤ r := by
  -- Away from the codiscrete set where `f` does not vanish, `f′ = f · (f′/f)`.
  have h₁ : deriv f =ᶠ[codiscrete ℂ] f * logDeriv f := by
    filter_upwards [(meromorphicOn_univ.2 hf).ne_zero_mem_codiscreteWithin fun x _ ↦ h' x]
      with z hz
    rw [Pi.mul_apply, logDeriv_apply, mul_div_cancel₀ _ hz]
  calc proximity (deriv f) ⊤ r
      = proximity (f * logDeriv f) ⊤ r := proximity_congr_codiscrete h₁ hr
    _ ≤ proximity f ⊤ r + proximity (logDeriv f) ⊤ r := by
        simpa using proximity_mul_top_le hf (fun x ↦ (hf x).logDeriv) r

/-!
## D4: The Integrated Separation Bound
-/

/--
**Integrated separation bound**: for a finite set `s` of targets, the total proximity of
`f` to the targets is controlled by the proximity of `1/f′` to `⊤` plus the proximity of
the shifted logarithmic derivatives to `⊤`, up to a constant depending only on `s`:
`Σₐ m(r, a) ≤ m(r, 1/f′) + Σₐ m(r, f′/(f - a)) + c`. This is the integrated form of the
separation lemma `Real.exists_sum_posLog_norm_inv_sub_le`.
-/
theorem sum_proximity_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (h' : ∀ x, meromorphicOrderAt (deriv f) x ≠ ⊤) (s : Finset ℂ) :
    ∃ c, ∀ r : ℝ, 1 ≤ r →
      ∑ a ∈ s, proximity f a r
        ≤ proximity (deriv f)⁻¹ ⊤ r + ∑ a ∈ s, proximity (logDeriv (f · - a)) ⊤ r + c := by
  obtain ⟨C, hC⟩ := Real.exists_sum_posLog_norm_inv_sub_le s
  refine ⟨C + Real.log s.card, fun r hr ↦ ?_⟩
  have hr0 : r ≠ 0 := (one_pos.trans_le hr).ne'
  have hd : Meromorphic (deriv f) := hf.deriv
  -- The auxiliary function `F = Σₐ 1/(f - a)` and integrability of all relevant
  -- functions on the circle of radius `r`
  set F : ℂ → ℂ := fun z ↦ ∑ a ∈ s, (f z - a)⁻¹ with hF_def
  have hFm : Meromorphic F := by fun_prop
  have hint : ∀ a ∈ s, CircleIntegrable (fun z ↦ log⁺ ‖f z - a‖⁻¹) 0 r := by
    intro a _
    have h₁ : Meromorphic (fun z ↦ (f z - a)⁻¹) := by fun_prop
    simpa [norm_inv] using h₁.meromorphicOn.circleIntegrable_posLog_norm
  have hFint : CircleIntegrable (log⁺ ‖F ·‖) 0 r :=
    hFm.meromorphicOn.circleIntegrable_posLog_norm
  -- Step 1: the total proximity is a single circle average.
  have step1 : ∑ a ∈ s, proximity f a r
      = circleAverage (fun z ↦ ∑ a ∈ s, log⁺ ‖f z - a‖⁻¹) 0 r := by
    rw [circleAverage_fun_sum hint]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [proximity_coe]
  -- Step 2: apply the separation lemma pointwise on the circle. Thanks to the junk-value
  -- convention `(0 : ℝ)⁻¹ = 0`, the pointwise bound holds without exceptional points.
  have step2 : circleAverage (fun z ↦ ∑ a ∈ s, log⁺ ‖f z - a‖⁻¹) 0 r
      ≤ proximity F ⊤ r + C := by
    rw [proximity_top]
    calc circleAverage (fun z ↦ ∑ a ∈ s, log⁺ ‖f z - a‖⁻¹) 0 r
        ≤ circleAverage (fun z ↦ log⁺ ‖F z‖ + C) 0 r := by
          apply circleAverage_mono (CircleIntegrable.fun_sum s hint)
            (hFint.add (circleIntegrable_const C 0 r))
          exact fun z _ ↦ hC (f z)
      _ = circleAverage (log⁺ ‖F ·‖) 0 r + C := by
          rw [circleAverage_fun_add hFint (circleIntegrable_const C 0 r),
            circleAverage_const]
  -- Step 3: away from the codiscrete set where `f′` does not vanish,
  -- `F = (1/f′) · Σₐ f′/(f - a)`; the identity survives Lean's junk-value conventions
  -- even at points with `f z = a`.
  have step3 : proximity F ⊤ r
      = proximity ((deriv f)⁻¹ * ∑ a ∈ s, logDeriv (f · - a)) ⊤ r := by
    apply proximity_congr_codiscrete _ hr0
    filter_upwards [(meromorphicOn_univ.2 hd).ne_zero_mem_codiscreteWithin fun x _ ↦ h' x]
      with z hz
    simp only [hF_def, Pi.mul_apply, Pi.inv_apply, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [logDeriv_apply, deriv_sub_const, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ hz, one_mul]
  -- Step 4: split the product and the sum into individual proximity functions.
  have hld : ∀ a ∈ s, Meromorphic (logDeriv (f · - a)) :=
    fun a _ x ↦ ((hf x).sub (.const a x)).logDeriv
  have step4 : proximity ((deriv f)⁻¹ * ∑ a ∈ s, logDeriv (f · - a)) ⊤ r
      ≤ proximity (deriv f)⁻¹ ⊤ r + ∑ a ∈ s, proximity (logDeriv (f · - a)) ⊤ r
        + Real.log s.card := by
    have h₁ := proximity_sum_top_le s (fun a ↦ logDeriv (f · - a)) hld r
    simp only [Pi.add_apply, Finset.sum_apply] at h₁
    have h₂ := proximity_mul_top_le hd.inv (Meromorphic.sum hld) r
    simp only [Pi.add_apply] at h₂
    linarith
  linarith [step1, step2, step3, step4]

end ValueDistribution
