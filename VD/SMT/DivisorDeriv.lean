/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Order
import VD.SMT.TruncatedCounting

/-!
# The Divisor of the Derivative — SMT work package B

See `VD/SMT/PLAN-SecondMainTheorem.md`, §4.

Mathlib target: new file `Mathlib/Analysis/Meromorphic/DivisorDeriv.lean`.
Dependencies: `VD/SMT/TruncatedCounting.lean` (package A).

This is the material explicitly reserved for the Second Main Theorem by the docstring of
`VD/LLD/MeromorphicLogDeriv.lean`.  It computes the zero- and pole-divisors of `deriv f` in
terms of those of `f`, and converts the ramification term of the Second Main Theorem into
truncated counting functions.

## Main results

- `meromorphicOrderAt_deriv_eq_top` / `meromorphicOrderAt_deriv_nonneg`: infinite resp.
  nonnegative meromorphic order propagates to the derivative.
- `MeromorphicOn.negPart_divisor_deriv`: the poles of `deriv f` are exactly the poles of
  `f`, with multiplicity increased by one.
- `MeromorphicOn.posPart_divisor_sub_trunc_le_divisor_deriv` and its several-targets
  version: an `a`-point of `f` of multiplicity `m` is a zero of `deriv f` of multiplicity
  `m - 1`.
- `ValueDistribution.logCounting_deriv_top` and
  `ValueDistribution.sum_logCounting_sub_truncatedLogCounting_le`: the counting-function
  form used by the Second Main Theorem.
-/

open Filter Function MeromorphicOn Metric Real Set Topology

/-!
## Order of the Derivative at a Point
-/

section OrderLevel

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {x : 𝕜}

/-- Derivatives of locally vanishing functions vanish locally: if `f` has infinite
meromorphic order at `x`, then so does `deriv f`. -/
theorem meromorphicOrderAt_deriv_eq_top {f : 𝕜 → E} (h : meromorphicOrderAt f x = ⊤) :
    meromorphicOrderAt (deriv f) x = ⊤ := by
  rw [meromorphicOrderAt_eq_top_iff] at h ⊢
  have h' : f =ᶠ[𝓝[≠] x] 0 := by filter_upwards [h] with z hz; simpa using hz
  filter_upwards [h'.nhdsNE_deriv] with z hz
  simpa using hz

/-- Where a meromorphic function has nonnegative order, so does its derivative. -/
theorem meromorphicOrderAt_deriv_nonneg [CompleteSpace E] [CharZero 𝕜] {f : 𝕜 → E}
    (hf : MeromorphicAt f x) (h : 0 ≤ meromorphicOrderAt f x) :
    0 ≤ meromorphicOrderAt (deriv f) x := by
  by_cases htop : meromorphicOrderAt f x = ⊤
  · rw [meromorphicOrderAt_deriv_eq_top htop]; exact le_top
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
  rw [← hn] at h
  have hn0 : 0 ≤ n := by exact_mod_cast h
  rcases eq_or_lt_of_le hn0 with h1 | h1
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ :=
      (meromorphicOrderAt_eq_int_iff (n := 0) hf).1 (by rw [← hn]; norm_cast; omega)
    have h₄ : f =ᶠ[𝓝[≠] x] g := by filter_upwards [h₃g] with z hz; simpa using hz
    rw [meromorphicOrderAt_congr h₄.nhdsNE_deriv]
    exact h₁g.deriv.meromorphicOrderAt_nonneg
  · have hne : (n : 𝕜) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [meromorphicOrderAt_deriv_eq_sub_one hne hn.symm]
    exact_mod_cast (by omega : (0 : ℤ) ≤ n - 1)

/-- At most one target value is attained at any point: if `f - a` has positive order at `x`,
then `f - b` has order zero there for every `b ≠ a`. -/
theorem meromorphicOrderAt_sub_const_eq_zero_of_ne {f : 𝕜 → 𝕜} {a b : 𝕜} {x : 𝕜} (hab : b ≠ a)
    (h : 0 < meromorphicOrderAt (f · - a) x) :
    meromorphicOrderAt (f · - b) x = 0 := by
  classical
  have hconst : meromorphicOrderAt (fun _ : 𝕜 ↦ a - b) x = 0 := by
    rw [meromorphicOrderAt_const]
    simp [sub_ne_zero.mpr hab.symm]
  have hmero : MeromorphicAt (f · - a) x := meromorphicAt_of_meromorphicOrderAt_ne_zero h.ne'
  have hsplit : (f · - b) = (fun _ : 𝕜 ↦ a - b) + (f · - a) := by
    ext z; simp only [Pi.add_apply]; ring
  rw [hsplit, meromorphicOrderAt_add_eq_left_of_lt hmero (by rw [hconst]; exact h), hconst]

end OrderLevel

/-!
## Divisor of the Derivative
-/

namespace MeromorphicOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜}

/-- **Pole divisor of the derivative**: the poles of `deriv f` are exactly the poles of `f`,
with multiplicity increased by exactly one. -/
theorem negPart_divisor_deriv [CompleteSpace 𝕜] [CharZero 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 → E}
    (hf : MeromorphicOn f U) :
    (divisor (deriv f) U)⁻ = (divisor f U)⁻ + ((divisor f U)⁻).trunc := by
  ext z
  by_cases hz : z ∈ U
  · by_cases htop : meromorphicOrderAt f z = ⊤
    · have hd := meromorphicOrderAt_deriv_eq_top htop
      simp [locallyFinsuppWithin.negPart_apply, locallyFinsuppWithin.trunc_apply,
        divisor_apply hf hz, divisor_apply hf.deriv hz, htop, hd]
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
      by_cases hsign : 0 ≤ n
      · have hd : 0 ≤ meromorphicOrderAt (deriv f) z :=
          meromorphicOrderAt_deriv_nonneg (hf z hz) (by rw [← hn]; exact_mod_cast hsign)
        have h2 : 0 ≤ (meromorphicOrderAt (deriv f) z).untop₀ := WithTop.untop₀_nonneg.mpr hd
        simp only [locallyFinsuppWithin.negPart_apply, locallyFinsuppWithin.coe_add,
          Pi.add_apply, locallyFinsuppWithin.trunc_apply, divisor_apply hf hz,
          divisor_apply hf.deriv hz, ← hn, WithTop.untop₀_coe]
        simp only [negPart]
        omega
      · rw [not_le] at hsign
        have hne : (n : 𝕜) ≠ 0 := by exact_mod_cast hsign.ne
        have hd : meromorphicOrderAt (deriv f) z = ↑(n - 1) :=
          meromorphicOrderAt_deriv_eq_sub_one hne hn.symm
        simp only [locallyFinsuppWithin.negPart_apply, locallyFinsuppWithin.coe_add,
          Pi.add_apply, locallyFinsuppWithin.trunc_apply, divisor_apply hf hz,
          divisor_apply hf.deriv hz, ← hn, hd, WithTop.untop₀_coe]
        simp only [negPart]
        omega
  · simp [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-- **Zero divisor of the derivative**, one target: an `a`-point of `f` of multiplicity `m` is
a zero of `deriv f` of multiplicity `m - 1`. -/
theorem posPart_divisor_sub_trunc_le_divisor_deriv [CompleteSpace 𝕜] [CharZero 𝕜]
    {f : 𝕜 → 𝕜} {a : 𝕜} (hf : MeromorphicOn f U) :
    (divisor (f · - a) U)⁺ - ((divisor (f · - a) U)⁺).trunc ≤ (divisor (deriv f) U)⁺ := by
  have hfa : MeromorphicOn (f · - a) U := hf.sub (.const a)
  have hderiv : deriv (f · - a) = deriv f := funext fun z ↦ deriv_sub_const a
  rw [Function.locallyFinsuppWithin.le_def]
  intro z
  by_cases hz : z ∈ U
  · by_cases htop : meromorphicOrderAt (f · - a) z = ⊤
    · simp [locallyFinsuppWithin.posPart_apply, locallyFinsuppWithin.trunc_apply,
        divisor_apply hfa hz, htop]
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
      by_cases hn1 : 1 ≤ n
      · have hne : (n : 𝕜) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        have hd : meromorphicOrderAt (deriv f) z = ↑(n - 1) := by
          rw [← hderiv]; exact meromorphicOrderAt_deriv_eq_sub_one hne hn.symm
        simp only [locallyFinsuppWithin.coe_sub, Pi.sub_apply, locallyFinsuppWithin.posPart_apply,
          locallyFinsuppWithin.trunc_apply, divisor_apply hfa hz, divisor_apply hf.deriv hz,
          ← hn, hd, WithTop.untop₀_coe]
        simp only [posPart]
        omega
      · rw [not_le] at hn1
        simp only [locallyFinsuppWithin.coe_sub, Pi.sub_apply, locallyFinsuppWithin.posPart_apply,
          locallyFinsuppWithin.trunc_apply, divisor_apply hfa hz, ← hn, WithTop.untop₀_coe]
        simp only [posPart]
        omega
  · simp [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-- **Zero divisor of the derivative**, several targets: multiple `aⱼ`-points of `f` are zeros
of `deriv f`, since at most one target is attained at any given point. -/
theorem sum_posPart_divisor_sub_trunc_le_divisor_deriv [CompleteSpace 𝕜] [CharZero 𝕜]
    {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (s : Finset 𝕜) :
    ∑ a ∈ s, ((divisor (f · - a) U)⁺ - ((divisor (f · - a) U)⁺).trunc)
      ≤ (divisor (deriv f) U)⁺ := by
  rw [Function.locallyFinsuppWithin.le_def]
  intro z
  simp only [locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  by_cases hz : z ∈ U
  · by_cases H : ∃ a₀ ∈ s, 0 < meromorphicOrderAt (f · - a₀) z
    · obtain ⟨a₀, ha₀s, ha₀⟩ := H
      rw [Finset.sum_eq_single a₀]
      · exact (Function.locallyFinsuppWithin.le_def.1
          (posPart_divisor_sub_trunc_le_divisor_deriv hf)) z
      · intro b hbs hba₀
        have hfb : MeromorphicOn (f · - b) U := hf.sub (.const b)
        have : meromorphicOrderAt (f · - b) z = 0 :=
          meromorphicOrderAt_sub_const_eq_zero_of_ne hba₀ ha₀
        simp [locallyFinsuppWithin.posPart_apply, locallyFinsuppWithin.trunc_apply,
          divisor_apply hfb hz, this]
      · intro h; exact absurd ha₀s h
    · simp only [not_exists, not_and, not_lt] at H
      apply le_trans (le_of_eq (Finset.sum_eq_zero ?_))
      · simp only [locallyFinsuppWithin.posPart_apply]; exact posPart_nonneg _
      · intro a ha
        have hfa : MeromorphicOn (f · - a) U := hf.sub (.const a)
        have hle : meromorphicOrderAt (f · - a) z ≤ 0 := H a ha
        have hthis : (divisor (f · - a) U z) ≤ 0 := by
          rw [divisor_apply hfa hz]
          simpa using WithTop.untop₀_le_untop₀ (by simp) hle
        simp only [locallyFinsuppWithin.coe_sub, Pi.sub_apply, locallyFinsuppWithin.posPart_apply,
          locallyFinsuppWithin.trunc_apply]
        simp only [posPart]
        omega
  · rw [Finset.sum_eq_zero (fun a _ ↦ locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz)]
    simp [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

end MeromorphicOn

/-!
## Counting-Function Corollaries
-/

namespace ValueDistribution

/-- `N(r, f′) = N(r, f) + N̄(r, f)`: the poles of `deriv f` are exactly the poles of `f`, each
with multiplicity increased by one. -/
theorem logCounting_deriv_top {f : ℂ → ℂ} (hf : Meromorphic f) :
    logCounting (deriv f) ⊤ = logCounting f ⊤ + truncatedLogCounting f ⊤ := by
  rw [logCounting_top, logCounting_top, truncatedLogCounting_top,
    (meromorphicOn_univ.2 hf).negPart_divisor_deriv, map_add]

/-- `Σⱼ (N(r, aⱼ) − N̄(r, aⱼ)) ≤ N(r, 1/f′)`: the `aⱼ`-points of `f`, counted with
multiplicity beyond the first, are zeros of `deriv f`. -/
theorem sum_logCounting_sub_truncatedLogCounting_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (s : Finset ℂ) {r : ℝ} (hr : 1 ≤ r) :
    ∑ a ∈ s, (logCounting f a r - truncatedLogCounting f a r) ≤ logCounting (deriv f) 0 r := by
  have key : ∀ a : ℂ, logCounting f a r - truncatedLogCounting f a r
      = ((divisor (f · - a) univ)⁺ - ((divisor (f · - a) univ)⁺.trunc)).logCounting r := by
    intro a
    rw [logCounting_coe, truncatedLogCounting_coe, map_sub]
    rfl
  rw [Finset.sum_congr rfl (fun a _ ↦ key a), ← Finset.sum_apply, ← map_sum, logCounting_zero]
  exact locallyFinsuppWithin.logCounting_le
    ((meromorphicOn_univ.2 hf).sum_posPart_divisor_sub_trunc_le_divisor_deriv s) hr

end ValueDistribution
