/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
--module

import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import VD.MathlibPending.LogCounting
import VD.MathlibPending.Single

open Asymptotics Filter Function Real Set Classical

/-!
# Asymptotic Behavior of the Logarithmic Counting Function

If `f` is meromorphic over a field `𝕜`, we show that the logarithmic counting
function for the poles of `f` is asymptotically bounded if and only if `f` has
only removable singularities.  See Page 170f of [Lang, *Introduction to Complex
Hyperbolic Spaces*][MR886677] for a detailed discussion.

## Implementation Notes

We establish the result first for the logarithmic counting function first for
functions with locally finite support on `𝕜` and then specializes to the
setting where the function with locally finite support is the pole or
zero-divisor of a meromorphic function.

## TODO

Establish the analogous characterization of meromorphic functions with finite
set of poles, as functions whose logarithmic counting function big-O of `log`.
-/

namespace Function.locallyFinsuppWithin

variable
  {E : Type*} [NormedAddCommGroup E]

/-!
## Logarithmic Counting Functions for Functions with Locally Finite Support
-/

/--
Qualitative consequence of `logCounting_single_eq_log_sub_const`. The constant
function `1 : ℝ → ℝ` is little o of the logarithmic counting function attached
to `single e`.
-/
lemma one_isLittleO_logCounting_single [ProperSpace E] {e : E} :
    (1 : ℝ → ℝ) =o[atTop] logCounting (single e) := by
  rw [isLittleO_iff]
  intro c hc
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, norm_eq_abs, eventually_atTop,
    ge_iff_le]
  use exp (|log ‖e‖| + c⁻¹)
  intro b hb
  have h₁b : 1 ≤ b := by
    calc 1
      _ ≤ exp (|log ‖e‖| + c⁻¹) :=
        one_le_exp (add_nonneg (abs_nonneg (log ‖e‖)) (inv_pos.2 hc).le)
      _ ≤ b := hb
  have h₁c : ‖e‖ ≤ exp (|log ‖e‖| + c⁻¹) := by
    calc ‖e‖
      _ ≤ exp (log ‖e‖) := by
        by_cases he : ‖e‖ = 0
        · simp [he]
        · simp_all [exp_log]
      _ ≤ exp (|log ‖e‖| + c⁻¹) :=
        exp_monotone (le_add_of_le_of_nonneg (le_abs_self _) (inv_pos.2 hc).le)
  rw [← inv_mul_le_iff₀ hc, mul_one, abs_of_nonneg (logCounting_nonneg single_pos.le h₁b)]
  calc c⁻¹
    _ ≤ logCounting (single e) (exp (|log ‖e‖| + c⁻¹)) := by
      simp [logCounting_single_eq_log_sub_const h₁c, le_sub_iff_add_le', le_abs_self (log ‖e‖)]
    _ ≤ logCounting (single e) b := by
      apply logCounting_mono single_pos.le (mem_Ioi.2 (exp_pos _)) _ hb
      simpa [mem_Ioi] using one_pos.trans_le h₁b

/--
A non-negative function with locally finite support is zero if and only if its
logarithmic counting functions is asymptotically bounded.
-/
lemma zero_iff_logCounting_bounded [ProperSpace E] {D : locallyFinsuppWithin (univ : Set E) ℤ}
    (h : 0 ≤ D) :
    D = 0 ↔ logCounting D =O[atTop] (1 : ℝ → ℝ) := by
  constructor
  · intro h₂
    simp [isBigO_of_le' (c := 0), h₂]
  · contrapose
    intro h₁
    obtain ⟨e, he⟩ := exists_single_le_pos (lt_of_le_of_ne h (h₁ ·.symm))
    rw [isBigO_iff'']
    push_neg
    intro a ha
    simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, norm_eq_abs, frequently_atTop,
      ge_iff_le]
    intro b
    obtain ⟨c, hc⟩ := eventually_atTop.1
      (isLittleO_iff.1 (one_isLittleO_logCounting_single (e := e)) ha)
    let ℓ := 1 + max ‖e‖ (max |b| |c|)
    have h₁ℓ : b < ℓ := by
      calc b
        _ ≤ |b| := le_abs_self _
        _ ≤ max |b| |c| := le_max_left _ _
        _ ≤ max ‖e‖ (max |b| |c|) := le_max_right _ _
        _ < 1 + max ‖e‖ (max |b| |c|) := lt_one_add _
        _ = ℓ := rfl
    have h₂ℓ : c < ℓ := by
      calc c
        _ ≤ |c| := le_abs_self _
        _ ≤ max |b| |c| := le_max_right _ _
        _ ≤ max ‖e‖ (max |b| |c|) := le_max_right _ _
        _ < 1 + max ‖e‖ (max |b| |c|) := lt_one_add _
        _ = ℓ := rfl
    have h₃ℓ : 1 ≤ ℓ := by simp [ℓ]
    have h₄ℓ : ℓ > ‖e‖ := by
      calc ‖e‖
        _ ≤ max ‖e‖ (max |b| |c|) := le_max_left _ _
        _ < 1 + max ‖e‖ (max |b| |c|) := lt_one_add _
        _ = ℓ := rfl
    use 1 + ℓ, h₁ℓ.le.trans (lt_one_add ℓ).le
    calc 1
      _ ≤ (a * |logCounting (single e) ℓ|) := by simpa [h₂ℓ.le] using hc ℓ
      _ ≤ (a * |logCounting D ℓ|) := by
        gcongr
        · apply logCounting_nonneg single_pos.le h₃ℓ
        · apply logCounting_le he h₃ℓ
      _ < a * |logCounting D (1 + ℓ)| := by
        gcongr 2
        rw [abs_of_nonneg (logCounting_nonneg h h₃ℓ),
          abs_of_nonneg (logCounting_nonneg h (le_add_of_nonneg_right (zero_le_one.trans h₃ℓ)))]
        apply logCounting_strictMono he h₄ℓ (h₄ℓ.trans (lt_one_add ℓ)) (lt_one_add ℓ)

end Function.locallyFinsuppWithin

namespace ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Logarithmic Counting Functions for the Poles of a Meromorphic Function
-/

/--
A meromorphic function has only removable singularities if and only if the
logarithmic counting function for its pole divisor is asymptotically bounded.
-/
theorem logCounting_isBigO_one_iff_analyticOnNhd {f : 𝕜 → E} (h : Meromorphic f) :
    logCounting f ⊤ =O[atTop] (1 : ℝ → ℝ) ↔ AnalyticOnNhd 𝕜 (toMeromorphicNFOn f ⊤) ⊤ := by
  simp only [logCounting, reduceDIte, top_eq_univ]
  rw [← Function.locallyFinsuppWithin.zero_iff_logCounting_bounded (negPart_nonneg _)]
  constructor
  · intro h₁f z hz
    apply (meromorphicNFOn_toMeromorphicNFOn f ⊤
      trivial).meromorphicOrderAt_nonneg_iff_analyticAt.1
    rw [meromorphicOrderAt_toMeromorphicNFOn h.meromorphicOn (by trivial), ← WithTop.untop₀_nonneg,
      ← h.meromorphicOn.divisor_apply (by trivial), ← negPart_eq_zero,
      ← locallyFinsuppWithin.negPart_apply]
    aesop
  · intro h₁f
    rwa [negPart_eq_zero, ← h.meromorphicOn.divisor_of_toMeromorphicNFOn,
      (meromorphicNFOn_toMeromorphicNFOn _ _).divisor_nonneg_iff_analyticOnNhd]

end ValueDistribution
