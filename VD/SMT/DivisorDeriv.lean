/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Truncated

/-!
# The Divisor of the Derivative — SMT work package B

See `VD/SMT/PLAN-SecondMainTheorem.md`, §4.

Mathlib targets (one PR, no new file):
- order-level lemmas: `Mathlib/Analysis/Meromorphic/Order.lean`,
- divisor-level results: `Mathlib/Analysis/Meromorphic/Divisor.lean`,
- counting-function corollaries:
  `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean`.

This file computes the zero- and pole-divisors of `deriv f` in terms of those of `f`, and converts
the ramification term of the Second Main Theorem into truncated counting functions.

## Main results

- `meromorphicOrderAt_deriv_eq_top` / `meromorphicOrderAt_deriv_nonneg`: infinite resp.
  nonnegative meromorphic order propagates to the derivative.
- `MeromorphicOn.negPart_divisor_deriv`: the poles of `deriv f` are exactly the poles of
  `f`, with multiplicity increased by one.
- `MeromorphicOn.posPart_divisor_sub_truncate_le_divisor_deriv` and its several-targets
  version: an `a`-point of `f` of multiplicity `m` is a zero of `deriv f` of multiplicity
  `m - 1`.
- `ValueDistribution.logCounting_deriv_top` and
  `ValueDistribution.sum_logCounting_sub_truncatedLogCounting_le`: the counting-function
  form used by the Second Main Theorem.
-/

@[expose] public section

open Filter Function MeromorphicOn Set Topology

/-!
## Order of the Derivative at a Point
-/

section OrderLevel

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜}

/-- Derivatives of locally vanishing functions vanish locally: if `f` has infinite
meromorphic order at `x`, then so does `deriv f`. -/
theorem meromorphicOrderAt_deriv_eq_top (h : meromorphicOrderAt f x = ⊤) :
    meromorphicOrderAt (deriv f) x = ⊤ := by
  rw [meromorphicOrderAt_eq_top_iff] at h ⊢
  filter_upwards [(show f =ᶠ[𝓝[≠] x] 0 from h).nhdsNE_deriv] with z hz using by simpa using hz

/-- Where a meromorphic function has nonnegative order, so does its derivative. -/
theorem meromorphicOrderAt_deriv_nonneg [CompleteSpace E] (hf : MeromorphicAt f x)
    (h : 0 ≤ meromorphicOrderAt f x) :
    0 ≤ meromorphicOrderAt (deriv f) x := by
  obtain ⟨g, hg, hfg⟩ := hf.meromorphicOrderAt_nonneg_iff.1 h
  rw [meromorphicOrderAt_congr hfg.nhdsNE_deriv]
  exact hg.deriv.meromorphicOrderAt_nonneg

/-- At most one target value is attained at any point: if `f - a` has positive order at `x`,
then `f - b` has order zero there for every `b ≠ a`. -/
theorem meromorphicOrderAt_sub_const_eq_zero_of_ne {a b : E} (hab : b ≠ a)
    (h : 0 < meromorphicOrderAt (f · - a) x) :
    meromorphicOrderAt (f · - b) x = 0 := by
  classical
  have hconst : meromorphicOrderAt (fun _ : 𝕜 ↦ a - b) x = 0 := by
    simp [meromorphicOrderAt_const, sub_ne_zero.mpr hab.symm]
  have hsplit : (f · - b) = (fun _ : 𝕜 ↦ a - b) + (f · - a) := by
    ext z; simp
  rw [hsplit, meromorphicOrderAt_add_eq_left_of_lt
    (meromorphicAt_of_meromorphicOrderAt_ne_zero h.ne') (by rwa [hconst]), hconst]

end OrderLevel

/-!
## Divisor of the Derivative
-/

namespace MeromorphicOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Pole divisor of the derivative**: the poles of `deriv f` are exactly the poles of `f`,
with multiplicity increased by exactly one. -/
theorem negPart_divisor_deriv [CompleteSpace E] [CharZero 𝕜] {f : 𝕜 → E}
    (hf : MeromorphicOn f U) :
    (divisor (deriv f) U)⁻ = (divisor f U)⁻ + ((divisor f U)⁻).truncate₁ := by
  ext z
  by_cases hz : z ∈ U
  · simp only [locallyFinsuppWithin.negPart_apply, locallyFinsuppWithin.coe_add, Pi.add_apply,
      locallyFinsuppWithin.truncate_apply, divisor_apply hf hz, divisor_apply hf.deriv hz]
    obtain h | h := le_or_gt 0 (meromorphicOrderAt f z)
    · -- No pole of `f` at `z`, hence no pole of `deriv f`.
      have h' := meromorphicOrderAt_deriv_nonneg (hf z hz) h
      simp [negPart_eq_zero.2 (WithTop.untop₀_nonneg.2 h),
        negPart_eq_zero.2 (WithTop.untop₀_nonneg.2 h')]
    · -- Pole of order `-n` at `z`: there, `deriv f` has a pole of order `-n + 1`.
      lift meromorphicOrderAt f z to ℤ using h.ne_top with n hn
      have hn₀ : n < 0 := mod_cast h
      rw [meromorphicOrderAt_deriv_eq_sub_one (mod_cast hn₀.ne) hn.symm]
      simp only [WithTop.untop₀_coe, negPart_def]
      omega
  · simp [hz]

/-- **Zero divisor of the derivative**, one target: an `a`-point of `f` of multiplicity `m` is
a zero of `deriv f` of multiplicity `m - 1`. -/
theorem posPart_divisor_sub_truncate_le_divisor_deriv [CompleteSpace E] [CharZero 𝕜]
    {f : 𝕜 → E} {a : E} (hf : MeromorphicOn f U) :
    (divisor (f · - a) U)⁺ - ((divisor (f · - a) U)⁺).truncate₁ ≤ (divisor (deriv f) U)⁺ := by
  have hfa : MeromorphicOn (f · - a) U := by fun_prop
  have hderiv : deriv (f · - a) = deriv f := funext fun z ↦ deriv_sub_const a
  rw [locallyFinsuppWithin.le_def]
  intro z
  by_cases hz : z ∈ U
  · simp only [locallyFinsuppWithin.coe_sub, Pi.sub_apply, locallyFinsuppWithin.posPart_apply,
      locallyFinsuppWithin.truncate_apply, divisor_apply hfa hz, divisor_apply hf.deriv hz]
    cases hn : meromorphicOrderAt (f · - a) z with
    | top => simp
    | coe n =>
      obtain h | h := le_or_gt n 0
      · -- No `a`-point at `z`: the left-hand side vanishes.
        simp [posPart_eq_zero.2 h]
      · -- An `a`-point of multiplicity `n` is a zero of `deriv f` of multiplicity `n - 1`.
        rw [← hderiv, meromorphicOrderAt_deriv_eq_sub_one (mod_cast h.ne') hn]
        simp only [WithTop.untop₀_coe, posPart_def]
        omega
  · simp [hz]

/-- **Zero divisor of the derivative**, several targets: multiple `a`-points of `f`, for `a`
in a finite set `s`, are zeros of `deriv f`, since at most one target is attained at any given
point. -/
theorem sum_posPart_divisor_sub_truncate_le_divisor_deriv [CompleteSpace E] [CharZero 𝕜]
    {f : 𝕜 → E} (hf : MeromorphicOn f U) (s : Finset E) :
    ∑ a ∈ s, ((divisor (f · - a) U)⁺ - ((divisor (f · - a) U)⁺).truncate₁) ≤
      (divisor (deriv f) U)⁺ := by
  rw [locallyFinsuppWithin.le_def]
  intro z
  simp only [locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  -- Targets `a` that are not attained at `z` do not contribute to the sum.
  have hzero (a : E) (ha : meromorphicOrderAt (f · - a) z ≤ 0) :
      ((divisor (f · - a) U)⁺ - ((divisor (f · - a) U)⁺).truncate₁) z = 0 := by
    have : divisor (f · - a) U z ≤ 0 := by
      by_cases hz : z ∈ U
      · rw [divisor_apply (by fun_prop) hz]
        simpa using WithTop.untop₀_le_untop₀ (by simp) ha
      · simp [hz]
    simp [posPart_eq_zero.2 this]
  by_cases! H : ∃ a₀ ∈ s, 0 < meromorphicOrderAt (f · - a₀) z
  · -- At most one target `a₀` is attained at `z`.
    obtain ⟨a₀, ha₀s, ha₀⟩ := H
    rw [Finset.sum_eq_single_of_mem a₀ ha₀s fun b _ hb ↦
      hzero b (meromorphicOrderAt_sub_const_eq_zero_of_ne hb ha₀).le]
    exact locallyFinsuppWithin.le_def.1 (posPart_divisor_sub_truncate_le_divisor_deriv hf) z
  · exact (Finset.sum_eq_zero fun a ha ↦ hzero a (H a ha)).trans_le (by simp [posPart_nonneg])

end MeromorphicOn

/-!
## Counting-Function Corollaries
-/

namespace ValueDistribution

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E}

/--
The poles of `deriv f` are exactly the poles of `f`, each with multiplicity increased by one:
the counting function for the poles of `deriv f` is the sum of the counting function and the
truncated counting function for the poles of `f`.
-/
theorem logCounting_deriv_top [CompleteSpace E] [CharZero 𝕜] (hf : Meromorphic f) :
    logCounting (deriv f) ⊤ = logCounting f ⊤ + truncatedLogCounting f ⊤ := by
  rw [logCounting_top, logCounting_top, truncatedLogCounting_top,
    hf.meromorphicOn.negPart_divisor_deriv, map_add]

/--
The `a`-points of `f`, for `a` in a finite set `s` and counted with multiplicity beyond the first,
are zeros of `deriv f`: for `1 ≤ r`, the differences between the counting functions and the
truncated counting functions for the `a`-points of `f` sum up to at most the counting function for
the zeros of `deriv f`.
-/
theorem sum_logCounting_sub_truncatedLogCounting_le [CompleteSpace E] [CharZero 𝕜]
    (hf : Meromorphic f) (s : Finset E) {r : ℝ} (hr : 1 ≤ r) :
    ∑ a ∈ s, (logCounting f a r - truncatedLogCounting f a r) ≤ logCounting (deriv f) 0 r := by
  calc ∑ a ∈ s, (logCounting f a r - truncatedLogCounting f a r)
    _ = (∑ a ∈ s, ((divisor (f · - a) univ)⁺ - (divisor (f · - a) univ)⁺.truncate₁)).logCounting
        r := by
      simp [logCounting_coe, truncatedLogCounting_coe]
    _ ≤ (divisor (deriv f) univ)⁺.logCounting r :=
      locallyFinsuppWithin.logCounting_le
        (hf.meromorphicOn.sum_posPart_divisor_sub_truncate_le_divisor_deriv s) hr
    _ = logCounting (deriv f) 0 r := by rw [logCounting_zero]

end ValueDistribution
