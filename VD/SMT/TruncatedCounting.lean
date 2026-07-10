/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

/-!
# Truncated Divisors and Truncated Counting Functions — SMT work package A

See `VD/SMT/PLAN-SecondMainTheorem.md`, §3.

Mathlib target: extend `Mathlib/Topology/LocallyFinsupp.lean` (the truncation operator)
plus new file `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean`
(the counting layer).
Dependencies: none (independently PR-able).

Contents:

- `Function.locallyFinsuppWithin.trunc`: truncation of an integer-valued function with
  locally finite support at multiplicity one, `z ↦ min (D z) 1`. This cannot be a lattice
  operation within `locallyFinsuppWithin U ℤ` because the constant function `1` does not
  have locally finite support; the definition imitates the existing `Min` instance,
  reusing `D`'s local-finiteness witnesses.

- `ValueDistribution.truncatedLogCounting`: the truncated logarithmic counting function
  `N̄(r, a)` of value distribution theory — like `logCounting f a`, but counting each
  zero/pole once, regardless of multiplicity.

The truncated counting function is the quantity through which the Second Main Theorem
(`VD/SMT/SecondMainTheorem.lean`) is classically stated.
-/

open Filter Function MeromorphicOn Metric Real Set

/-!
## Truncation of a Function with Locally Finite Support
-/

namespace Function.locallyFinsuppWithin

variable {X : Type*} [TopologicalSpace X] {U : Set X}

/--
Truncation of an integer-valued function with locally finite support: the pointwise
minimum with the constant `1`.  This is *not* a lattice operation within
`locallyFinsuppWithin U ℤ`, because the constant function `1` does not have locally finite
support.
-/
noncomputable def trunc (D : locallyFinsuppWithin U ℤ) : locallyFinsuppWithin U ℤ where
  toFun z := min (D z) 1
  supportWithinDomain' := by
    intro x
    contrapose
    intro hx
    simp [notMem_support.1 fun a ↦ hx (D.supportWithinDomain a)]
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    obtain ⟨t, ht⟩ := D.supportLocallyFiniteWithinDomain z hz
    refine ⟨t, ht.1, ht.2.subset ?_⟩
    intro a ha
    simp only [mem_inter_iff, mem_support, ne_eq] at ha ⊢
    refine ⟨ha.1, ?_⟩
    intro hCon
    simp [hCon] at ha

@[simp] lemma trunc_apply (D : locallyFinsuppWithin U ℤ) (z : X) :
    D.trunc z = min (D z) 1 := rfl

lemma trunc_le (D : locallyFinsuppWithin U ℤ) (_h : 0 ≤ D) : D.trunc ≤ D := by
  rw [le_def]
  intro z
  simp only [trunc_apply]
  exact min_le_left (D z) 1

lemma trunc_nonneg {D : locallyFinsuppWithin U ℤ} (h : 0 ≤ D) : 0 ≤ D.trunc := by
  rw [le_def]
  intro z
  simpa using le_min ((le_def.1 h) z) zero_le_one

lemma trunc_mono {D₁ D₂ : locallyFinsuppWithin U ℤ} (h : D₁ ≤ D₂) : D₁.trunc ≤ D₂.trunc := by
  rw [le_def]
  intro z
  simpa using min_le_min_right 1 ((le_def.1 h) z)

@[simp] lemma trunc_trunc (D : locallyFinsuppWithin U ℤ) : D.trunc.trunc = D.trunc := by
  ext z
  simp only [trunc_apply, min_assoc, min_self]

lemma support_trunc (D : locallyFinsuppWithin U ℤ) : D.trunc.support = D.support := by
  ext z
  simp only [Function.mem_support, ne_eq, trunc_apply]
  omega

/-!
## The Truncated Counting Function of a Function with Locally Finite Support
-/

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/--
For `1 ≤ r`, the counting function of a truncated divisor is bounded above by the counting
function of the divisor itself.
-/
theorem logCounting_trunc_le {D : locallyFinsupp E ℤ} (h : 0 ≤ D) {r : ℝ} (hr : 1 ≤ r) :
    logCounting D.trunc r ≤ logCounting D r :=
  logCounting_le (trunc_le D h) hr

/--
For `1 ≤ r`, the counting function of a truncated non-negative divisor is non-negative.
-/
theorem logCounting_trunc_nonneg {D : locallyFinsupp E ℤ} (h : 0 ≤ D) {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ logCounting D.trunc r :=
  logCounting_nonneg (trunc_nonneg h) hr

end Function.locallyFinsuppWithin

/-!
## The Truncated Logarithmic Counting Function of a Meromorphic Function
-/

namespace ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {a : WithTop E} {a₀ : E}

variable (f a) in
/--
The truncated logarithmic counting function `N̄(r, a)` of value distribution theory: like
`logCounting f a`, but counting each zero/pole once, regardless of multiplicity.  In the
special case where `a = ⊤`, it counts the poles of `f`, each with multiplicity one.
-/
noncomputable def truncatedLogCounting : ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact ((divisor f Set.univ)⁻.trunc).logCounting
  · exact ((divisor (f · - a.untop₀) Set.univ)⁺.trunc).logCounting

/--
The truncated logarithmic counting function `truncatedLogCounting f ⊤` counts the poles of
`f`, each with multiplicity one.
-/
lemma truncatedLogCounting_top :
    truncatedLogCounting f ⊤ = ((divisor f Set.univ)⁻.trunc).logCounting := by
  simp [truncatedLogCounting]

/--
For finite values `a₀`, the truncated logarithmic counting function `truncatedLogCounting f a₀`
counts the zeros of `f - a₀`, each with multiplicity one.
-/
lemma truncatedLogCounting_coe :
    truncatedLogCounting f a₀ = ((divisor (f · - a₀) Set.univ)⁺.trunc).logCounting := by
  simp [truncatedLogCounting]

/--
The truncated logarithmic counting function `truncatedLogCounting f 0` counts the zeros of
`f`, each with multiplicity one.
-/
lemma truncatedLogCounting_zero :
    truncatedLogCounting f 0 = ((divisor f Set.univ)⁺.trunc).logCounting := by
  simp only [truncatedLogCounting, WithTop.zero_ne_top, reduceDIte, WithTop.untop₀_zero, sub_zero]

/--
Evaluation of the truncated logarithmic counting function at zero yields zero.
-/
@[simp] lemma truncatedLogCounting_eval_zero :
    truncatedLogCounting f a 0 = 0 := by
  by_cases h : a = ⊤ <;> simp [truncatedLogCounting, h]

/--
For `1 ≤ r`, the truncated logarithmic counting function is bounded above by the ordinary
logarithmic counting function.
-/
theorem truncatedLogCounting_le {r : ℝ} (hr : 1 ≤ r) :
    truncatedLogCounting f a r ≤ logCounting f a r := by
  by_cases h : a = ⊤
  · subst h
    rw [truncatedLogCounting_top, logCounting_top]
    exact locallyFinsuppWithin.logCounting_trunc_le (negPart_nonneg _) hr
  · lift a to E using h with a₀
    rw [truncatedLogCounting_coe, logCounting_coe]
    exact locallyFinsuppWithin.logCounting_trunc_le (posPart_nonneg _) hr

/--
For `1 ≤ r`, the truncated logarithmic counting function is non-negative.
-/
theorem truncatedLogCounting_nonneg {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ truncatedLogCounting f a r := by
  by_cases h : a = ⊤
  · subst h
    rw [truncatedLogCounting_top]
    exact locallyFinsuppWithin.logCounting_trunc_nonneg (negPart_nonneg _) hr
  · lift a to E using h with a₀
    rw [truncatedLogCounting_coe]
    exact locallyFinsuppWithin.logCounting_trunc_nonneg (posPart_nonneg _) hr

/--
The truncated logarithmic counting function is monotonous.
-/
theorem truncatedLogCounting_monotoneOn :
    MonotoneOn (truncatedLogCounting f a) (Set.Ioi 0) := by
  by_cases h : a = ⊤
  · subst h
    rw [truncatedLogCounting_top]
    exact locallyFinsuppWithin.logCounting_mono
      (locallyFinsuppWithin.trunc_nonneg (negPart_nonneg _))
  · lift a to E using h with a₀
    rw [truncatedLogCounting_coe]
    exact locallyFinsuppWithin.logCounting_mono
      (locallyFinsuppWithin.trunc_nonneg (posPart_nonneg _))

/--
Relation between the truncated logarithmic counting functions of `f` and of `f⁻¹`.
-/
@[simp] theorem truncatedLogCounting_inv {f : 𝕜 → 𝕜} :
    truncatedLogCounting f⁻¹ ⊤ = truncatedLogCounting f 0 := by
  rw [truncatedLogCounting_top, truncatedLogCounting_zero]
  congr 1
  ext z
  simp [divisor_inv]

/--
If two functions differ only on a discrete set, then their truncated logarithmic counting
functions agree.
-/
theorem truncatedLogCounting_congr_codiscrete [NormedSpace ℂ E] {f g : ℂ → E}
    (hfg : f =ᶠ[codiscrete ℂ] g) :
    truncatedLogCounting f = truncatedLogCounting g := by
  ext a : 1
  by_cases h : a = ⊤
  · subst h
    rw [truncatedLogCounting_top, truncatedLogCounting_top,
      divisor_congr_codiscreteWithin hfg isOpen_univ]
  · lift a to E using h with a₀
    rw [truncatedLogCounting_coe, truncatedLogCounting_coe]
    congr 3
    exact divisor_congr_codiscreteWithin (by filter_upwards [hfg] using by simp) isOpen_univ

end ValueDistribution
