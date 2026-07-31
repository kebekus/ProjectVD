/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.LLD.LogDerivLemma
import VD.MathlibSubmitted.MeromorphicLogDeriv
import VD.MathlibSubmitted.SeparationLemma

/-!
# Proximity Estimates for the Second Main Theorem — SMT work package D

See `VD/SMT/PLAN-SecondMainTheorem.md`, §6.

Mathlib target: `Mathlib/Analysis/Complex/ValueDistribution/SecondMainTheorem.lean`
(part 1 of 3).
Dependencies: `VD/SMT/SeparationLemma.lean` (package C) and the Lemma on the Logarithmic
Derivative (`VD/LLD/LogDerivLemma.lean`).

This file collects the four proximity estimates from which the Second Main Theorem of
value distribution theory is assembled:

- D1, `MeromorphicOn.exists_eventuallyEq_const_iff_deriv_eventuallyEq_zero`: the
  constancy dichotomy — a function meromorphic on an open connected subset of `ℝ` or `ℂ`,
  with values in a complete normed space, is constant away from a discrete set iff its
  derivative vanishes away from a discrete set; the global version
  `Meromorphic.exists_eventuallyEq_const_iff_deriv_eventuallyEq_zero` is a corollary.
  This isolates the degenerate case of the hypothesis-free Second Main Theorem.

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
## D1: The Constancy Dichotomy

The degenerate case of the Second Main Theorem: a function meromorphic on an open
connected set is constant away from a discrete set if and only if its derivative vanishes
away from a discrete set — equivalently, by
`MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall_mem`, vanishes to infinite
order at a single point. This allows stating the Second Main Theorem without any
nondegeneracy hypothesis.
-/

/--
On an open set `U`, two functions agree along `codiscreteWithin U` if and only if they agree along
the punctured neighborhood of every point of `U`. Local version of
`eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE`.
-/
lemma eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE {X Y : Type*}
    [TopologicalSpace X] {U : Set X} (hU : IsOpen U) {f g : X → Y} :
    f =ᶠ[codiscreteWithin U] g ↔ ∀ x ∈ U, f =ᶠ[𝓝[≠] x] g := by
  rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  refine forall₂_congr fun x hx ↦
    ⟨fun h ↦ ?_, fun h ↦ mem_of_superset h subset_union_left⟩
  filter_upwards [h, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)] with z hz h₂z
  exact hz.resolve_right fun h₃z ↦ h₃z h₂z

/--
A function meromorphic on an open connected subset `U` of `ℝ` or `ℂ`, with values in a complete
normed space, is constant away from a discrete subset of `U` if and only if its derivative vanishes
away from a discrete subset of `U`. Meromorphic analogue of
`IsOpen.exists_is_const_of_fderiv_eq_zero`.
-/
theorem MeromorphicOn.exists_eventuallyEq_const_iff_deriv_eventuallyEq_zero
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] {f : 𝕜 → E} {U : Set 𝕜} (hf : MeromorphicOn f U) (h₁U : IsOpen U)
    (h₂U : IsConnected U) :
    (∃ c, f =ᶠ[codiscreteWithin U] fun _ ↦ c) ↔ deriv f =ᶠ[codiscreteWithin U] 0 := by
  constructor
  · -- Congruence in the codiscrete filter passes to derivatives, and constants have
    -- vanishing derivative.
    rintro ⟨c, hc⟩
    filter_upwards [deriv_congr_codiscreteWithin h₁U hc] with z hz
    simp [hz]
  · -- Vanishing derivative means: constant
    intro h
    obtain ⟨z₀, hz₀⟩ := h₂U.nonempty
    have h₀ : deriv f =ᶠ[𝓝[≠] z₀] 0 :=
      (eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE h₁U).1 h z₀ hz₀
    -- Step 1: `f` is constant on a punctured neighborhood of the base point `z₀`.
    obtain ⟨c, hc⟩ : ∃ c, f =ᶠ[𝓝[≠] z₀] fun _ ↦ c := by
      -- The meromorphic order of `f` at `z₀` is `0` or `⊤`, since any other order would
      -- force a finite order for `deriv f`.
      have horder : meromorphicOrderAt f z₀ = 0 ∨ meromorphicOrderAt f z₀ = ⊤ := by
        by_contra hcon
        push Not at hcon
        lift meromorphicOrderAt f z₀ to ℤ using hcon.2 with n hn
        rw [ne_eq, WithTop.coe_eq_zero, ←ne_eq] at hcon
        apply WithTop.coe_ne_top (a := n - 1)
        rw [← meromorphicOrderAt_deriv_eq_sub_one (Int.cast_ne_zero.2 hcon.1) hn.symm,
          meromorphicOrderAt_eq_top_iff.2 h₀]
      rcases horder with h₂ | h₂
      -- Order `0`: near `z₀`, the function `f` agrees with an analytic `g` whose derivative
      -- vanishes; by continuity, `deriv g = 0` on a ball, so `g` is constant there.
      · obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff (n := 0) (hf z₀ hz₀)).1 h₂
        rw [← Filter.EventuallyEq] at h₃g
        simp_rw [zpow_ofNat, pow_zero, one_smul] at h₃g
        have hdg : deriv g =ᶠ[𝓝[≠] z₀] 0 := h₃g.nhdsNE_deriv.symm.trans h₀
        have hdfull : ∀ᶠ z in 𝓝 z₀, deriv g z = 0 := by
          filter_upwards [eventually_nhdsWithin_iff.1 hdg] with z hz
          rcases eq_or_ne z z₀ with rfl | hne
          · apply tendsto_nhds_unique (l := 𝓝[≠] z) h₁g.deriv.continuousAt.continuousWithinAt
            rw [tendsto_congr' hdg]
            exact tendsto_const_nhds
          · exact hz hne
        obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1
          (hdfull.and h₁g.eventually_analyticAt)
        have hcball : ∀ z ∈ Metric.ball z₀ r, g z = g z₀ := by
          intro z hz
          apply (convex_ball z₀ r).is_const_of_fderivWithin_eq_zero
            (fun w hw ↦ (hball w hw).2.differentiableAt.differentiableWithinAt)
            (fun w hw ↦ ?_) hz (Metric.mem_ball_self hr)
          rw [fderivWithin_of_isOpen Metric.isOpen_ball hw]
          have h₅ : HasDerivAt g 0 w := by
            have := (hball w hw).2.differentiableAt.hasDerivAt
            rwa [(hball w hw).1] at this
          simpa using h₅.hasFDerivAt.fderiv
        refine ⟨g z₀, ?_⟩
        filter_upwards [h₃g,
          mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hr)] with z h₁z h₂z
        rw [h₁z, hcball z h₂z]
      -- Order `⊤`: `f` vanishes on a punctured neighborhood of `z₀`, and the constant is `0`.
      · exact ⟨0, meromorphicOrderAt_eq_top_iff.1 h₂⟩
    -- Step 2: `f - c` has order `⊤` at `z₀`, hence everywhere on `U` by connectedness.
    have h₃ : ∀ y ∈ U, meromorphicOrderAt (f · - c) y = ⊤ := by
      intro y hy
      by_contra h₂y
      have hF : MeromorphicOn (f · - c) U := fun x hx ↦ (hf x hx).sub (.const c x)
      apply (hF.exists_meromorphicOrderAt_ne_top_iff_forall_mem h₂U).1 ⟨y, hy, h₂y⟩ z₀ hz₀
      rw [meromorphicOrderAt_eq_top_iff]
      filter_upwards [hc] with z hz
      simp [hz]
    refine ⟨c, (eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE h₁U).2
      fun y hy ↦ ?_⟩
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 (h₃ y hy)] with z hz
    exact sub_eq_zero.1 hz

/--
A meromorphic function on `ℝ` or `ℂ`, with values in a complete normed space, is constant away from
a discrete set if and only if its derivative vanishes away from a discrete set. Meromorphic analogue
of `is_const_of_deriv_eq_zero`.
-/
theorem Meromorphic.exists_eventuallyEq_const_iff_deriv_eventuallyEq_zero
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] {f : 𝕜 → E} (hf : Meromorphic f) :
    (∃ c, f =ᶠ[codiscrete 𝕜] fun _ ↦ c) ↔ deriv f =ᶠ[codiscrete 𝕜] 0 :=
  (meromorphicOn_univ.2 hf).exists_eventuallyEq_const_iff_deriv_eventuallyEq_zero
    isOpen_univ isConnected_univ

namespace ValueDistribution

/-!
## D2: The Lemma on the Logarithmic Derivative for Shifted Targets
-/

/--
**Lemma on the Logarithmic Derivative, arbitrary finite targets**: for `f` meromorphic on the
complex plane and any value `a`, the proximity function of `logDeriv (f · - a)` for the value `⊤`
satisfies `m(r, f′/(f - a)) = O(log⁺ T(r, f) + log r)` as `r → ∞`, outside an exceptional set of
finite Lebesgue measure. Note that the error is expressed through the characteristic of `f` itself,
not that of `f - a`.
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
The proximity function of the derivative is bounded by that of the function plus that of the
logarithmic derivative: `m(r, f′) ≤ m(r, f) + m(r, f′/f)`.
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
**Integrated separation bound**: for a finite set `s` of targets, the total proximity of `f` to the
targets is controlled by the proximity of `1/f′` to `⊤` plus the proximity of the shifted
logarithmic derivatives to `⊤`, up to a constant depending only on `s`: `Σₐ m(r, a) ≤ m(r, 1/f′) +
Σₐ m(r, f′/(f - a)) + c`. This is the integrated form of the separation lemma
`Real.exists_sum_posLog_inv_norm_sub_le`.
-/
theorem sum_proximity_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (h' : ∀ x, meromorphicOrderAt (deriv f) x ≠ ⊤) (s : Finset ℂ) :
    ∃ c, ∀ r : ℝ, 1 ≤ r →
      ∑ a ∈ s, proximity f a r
        ≤ proximity (deriv f)⁻¹ ⊤ r + ∑ a ∈ s, proximity (logDeriv (f · - a)) ⊤ r + c := by
  obtain ⟨C, hC⟩ := Real.exists_sum_posLog_inv_norm_sub_le s
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
