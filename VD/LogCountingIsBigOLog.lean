/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Asymptotic

/-!
# The Logarithmic Counting Function and `O(log)`

If `f` is meromorphic over a field `𝕜`, we characterize the meromorphic functions with finite set of
poles as those functions whose logarithmic counting function for the poles is big-O of `log`.  This
is the asymptotic analogue, at the scale of `log`, of the boundedness characterization established
in `Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Asymptotic`.

## Implementation Notes

We establish the result first for the logarithmic counting function of functions with locally finite
support on `𝕜` and then specialize to the setting where the function with locally finite support is
the pole-divisor of a meromorphic function.
-/

open Asymptotics Filter Function MeromorphicOn Real Set

namespace Function.locallyFinsuppWithin

variable
  {E : Type*} [NormedAddCommGroup E]

/-!
## Logarithmic Counting Functions for Functions with Locally Finite Support
-/

/--
The logarithmic counting function of a singleton is big-O of `log`. This is the qualitative
consequence of `logCounting_single_eq_log_sub_const`.
-/
lemma logCounting_single_isBigO_log [DecidableEq E] [ProperSpace E] {e : E} {n : ℤ} :
    logCounting (single e n) =O[atTop] Real.log := by
  have h₁ : logCounting (single e n) =ᶠ[atTop] (fun r ↦ (n : ℝ) * log r - (n : ℝ) * log ‖e‖) := by
    filter_upwards [eventually_ge_atTop ‖e‖] with r hr
    rw [logCounting_single_eq_log_sub_const hr]
    ring
  have hb : (fun r ↦ (n : ℝ) * log r) =O[atTop] Real.log := isBigO_const_mul_self (n : ℝ) log atTop
  have ho : (fun _ : ℝ ↦ (n : ℝ) * log ‖e‖) =O[atTop] Real.log := isLittleO_const_log_atTop.isBigO
  exact (hb.sub ho).congr' h₁.symm EventuallyEq.rfl

/--
A function with finite support has a logarithmic counting function that is big-O of `log`. Note that
this direction does not require non-negativity.
-/
lemma logCounting_isBigO_log_of_finite_support [ProperSpace E]
    {D : locallyFinsupp E ℤ} (h : D.support.Finite) :
    logCounting D =O[atTop] Real.log := by
  classical
  set s := h.toFinset with hs
  have hD : D = ∑ z ∈ s, single z (D z) := by
    ext w
    simp only [coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq]
    by_cases hw : w ∈ s
    · simp [hw]
    · simp only [hw, if_false]
      have : w ∉ support D := by simpa only [hs, Set.Finite.mem_toFinset] using hw
      exact notMem_support.mp this
  rw [hD, map_sum]
  have hfun : (∑ z ∈ s, logCounting (single z (D z)))
      = fun r ↦ ∑ z ∈ s, logCounting (single z (D z)) r := by
    ext r; rw [Finset.sum_apply]
  rw [hfun]
  exact IsBigO.sum fun z _ ↦ logCounting_single_isBigO_log

/--
A non-negative function whose logarithmic counting function is big-O of `log` has finite support.
-/
lemma finite_support_of_logCounting_isBigO_log [ProperSpace E]
    {D : locallyFinsupp E ℤ} (h : 0 ≤ D) (hO : logCounting D =O[atTop] Real.log) :
    D.support.Finite := by
  classical
  by_contra hInf
  rw [Set.not_finite] at hInf
  obtain ⟨C, hC⟩ := isBigO_iff.1 hO
  obtain ⟨N, hCN⟩ := exists_nat_gt (max C 0)
  obtain ⟨t, htsub, htcard⟩ := hInf.exists_subset_card_eq N
  have hCN' : C < N := lt_of_le_of_lt (le_max_left C 0) hCN
  -- The auxiliary divisor `D'` is bounded above by `D`.
  set D' := ∑ z ∈ t, single z (1 : ℤ) with hD'
  have hle : D' ≤ D := by
    rw [le_def, Pi.le_def]
    intro w
    simp only [hD', coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq]
    by_cases hw : w ∈ t
    · simp only [hw, if_true]
      have h₁ : D w ≠ 0 := mem_support.mp (htsub (Finset.mem_coe.2 hw))
      have h₂ : (0 : ℤ) ≤ D w := by simpa using (le_def.1 h) w
      omega
    · simp only [hw, if_false]
      simpa using (le_def.1 h) w
  -- A uniform bound on the norms of points in `t`.
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, ∀ z ∈ t, ‖z‖ ≤ R₀ := by
    rcases t.eq_empty_or_nonempty with rfl | ht
    · exact ⟨0, by simp⟩
    · exact ⟨t.sup' ht (‖·‖), fun z hz ↦ Finset.le_sup' (‖·‖) hz⟩
  set K := ∑ z ∈ t, log ‖z‖ with hK
  -- Eventually, `logCounting D' = N * log - K`.
  have hEq : ∀ᶠ r in atTop, logCounting D' r = (N : ℝ) * log r - K := by
    filter_upwards [eventually_ge_atTop R₀] with r hr
    have hsum : logCounting D' r = ∑ z ∈ t, (log r - log ‖z‖) := by
      rw [hD', map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun z hz ↦ ?_
      simpa using logCounting_single_eq_log_sub_const (e := z) (n := 1) ((hR₀ z hz).trans hr)
    rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, htcard, nsmul_eq_mul, ← hK]
  -- Combine the bounds into a contradiction with `log → ∞`.
  have hFinal : ∀ᶠ r in atTop, ((N : ℝ) - C) * log r ≤ K := by
    filter_upwards [hEq, eventually_ge_atTop (1 : ℝ), hC] with r hr₁ hr₂ hr₃
    have h₂ : 0 ≤ logCounting D r := logCounting_nonneg h hr₂
    have h₁ : logCounting D' r ≤ logCounting D r := logCounting_le hle hr₂
    rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg h₂, abs_of_nonneg (log_nonneg hr₂)] at hr₃
    rw [hr₁] at h₁
    have hexp : ((N : ℝ) - C) * log r = (N : ℝ) * log r - C * log r := by ring
    rw [hexp]
    linarith [h₁, hr₃]
  have hTendsto : Tendsto (fun r ↦ ((N : ℝ) - C) * log r) atTop atTop :=
    Tendsto.const_mul_atTop (sub_pos.mpr hCN') tendsto_log_atTop
  obtain ⟨r, hr₁, hr₂⟩ := (hFinal.and (hTendsto.eventually_gt_atTop K)).exists
  linarith

/--
A non-negative function with locally finite support has finite support if and only if its
logarithmic counting function is big-O of `log`.
-/
theorem finite_support_iff_logCounting_isBigO_log [ProperSpace E]
    {D : locallyFinsupp E ℤ} (h : 0 ≤ D) :
    D.support.Finite ↔ logCounting D =O[atTop] Real.log :=
  ⟨logCounting_isBigO_log_of_finite_support, finite_support_of_logCounting_isBigO_log h⟩

end Function.locallyFinsuppWithin

namespace ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Logarithmic Counting Functions for the Poles of a Meromorphic Function
-/

/--
A meromorphic function has a finite set of poles if and only if the logarithmic counting function
for its pole-divisor is big-O of `log`.
-/
theorem logCounting_isBigO_log_iff_finite_support {f : 𝕜 → E} :
    logCounting f ⊤ =O[atTop] Real.log ↔ (divisor f univ)⁻.support.Finite := by
  rw [logCounting_top]
  exact (locallyFinsuppWithin.finite_support_iff_logCounting_isBigO_log (negPart_nonneg _)).symm

end ValueDistribution
