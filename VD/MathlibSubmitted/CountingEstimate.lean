/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

/-!
# Unintegrated Counting vs. Logarithmic Counting — LLD work package C3

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §5.

Mathlib target: extend `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean`.
Dependencies: none (independently PR-able).

For a nonnegative divisor `D` and radii `1 ≤ ρ < r`, the total mass of `D` on the closed ball of
radius `ρ`, weighted by `log (r / ρ)`, is bounded by the logarithmic counting function at radius
`r`. In the two-radius estimate for the Lemma on the Logarithmic Derivative, this bounds the
number of zeros and poles in the smaller disk in terms of the Nevanlinna characteristic at the
larger radius.

The file also provides the elementary helper `Real.sub_div_le_log_div`, which converts the
reciprocal `1 / log (r / ρ)` into the error terms `log r + log⁺ (r - ρ)⁻¹` during the final
assembly.
-/

open Function Metric Real Set


/-!
## The Counting Estimate
-/

namespace Function.locallyFinsuppWithin

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*}
  {E : Type*} [NormedAddCommGroup E]

/-- Restriction is monotone -/
lemma restrict_mono [Zero Y] [LinearOrder Y] {A B : locallyFinsuppWithin U Y}
    {V : Set X} (hVU : V ⊆ U) (hAB : A ≤ B) :
    A.restrict hVU ≤ B.restrict hVU := by
  intro z
  by_cases hz : z ∈ V
  · simp_all [restrict_apply, hAB z]
  · simp_all

/-- Restriction as an ordered group morphism -/
noncomputable def restrictOrderMonoidHom [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]
    {V : Set X} (h : V ⊆ U) :
    locallyFinsuppWithin U Y →+o locallyFinsuppWithin V Y where
  toFun D := D.restrict h
  map_zero' := by
    ext x
    simp [restrict_apply]
  map_add' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [restrict_apply, hx]
  monotone' _ _ hAB z := by
    apply restrict_mono h hAB

@[simp]
lemma restrictOrderMonoidHom_apply [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]
    {V : Set X} (D : locallyFinsuppWithin U Y) (h : V ⊆ U) :
    restrictOrderMonoidHom h D = D.restrict h := by rfl


/-- **Counting estimate**: for a nonnegative divisor `D` on `ℂ` and radii `1 ≤ ρ < r`, the total
mass of `D` on the closed ball of radius `ρ`, weighted by `log (r / ρ)`, is bounded by the
logarithmic counting function of `D` at radius `r`. -/
theorem sum_toClosedBall_le_logCounting {D : Function.locallyFinsupp ℂ ℤ} {ρ r : ℝ}
    (hD : 0 ≤ D) (hρ : 1 ≤ ρ) (hρr : ρ < r) :
    (∑ᶠ z, (D.toClosedBall ρ z : ℝ)) * Real.log (r / ρ) ≤ D.logCounting r := by
  have hr₀ : (0 : ℝ) < r := by linarith
  have habsρ : |ρ| = ρ := abs_of_pos (by linarith)
  have habsr : |r| = r := abs_of_pos hr₀
  have hD' : ∀ z, 0 ≤ D z := (by simpa using (le_def.1 hD) ·)
  -- `toClosedBall` inherits nonnegativity
  have hpos : ∀ s z, 0 ≤ D.toClosedBall s z := by
    intro s z
    by_cases hz : z ∈ closedBall (0 : ℂ) |s|
    · rw [toClosedBall_eval_within _ hz]
      exact hD' z
    · simp [toClosedBall, hz]
  -- The common finite index set
  have hfin : ((D.toClosedBall r).support).Finite :=
    finiteSupport _ (isCompact_closedBall 0 |r|)
  set t : Finset ℂ := insert 0 hfin.toFinset with ht_def
  have hmem : ∀ z : ℂ, D.toClosedBall r z ≠ 0 → z ∈ t := by
    intro z hz
    exact Finset.mem_insert_of_mem (hfin.mem_toFinset.2 hz)
  have hmemρ : ∀ z : ℂ, D.toClosedBall ρ z ≠ 0 → z ∈ t := by
    intro z hz
    by_cases h : z ∈ closedBall (0 : ℂ) |ρ|
    · apply hmem
      rw [toClosedBall_eval_within _ (by
        rw [mem_closedBall_zero_iff, habsr]
        exact le_trans (by rwa [mem_closedBall_zero_iff, habsρ] at h) hρr.le)]
      rwa [toClosedBall_eval_within _ h] at hz
    · simp_all [toClosedBall]
  -- Rewrite both sides as finite sums over `t`
  have hLHS : (∑ᶠ z, (D.toClosedBall ρ z : ℝ)) = ∑ z ∈ t, (D.toClosedBall ρ z : ℝ) := by
    apply finsum_eq_sum_of_support_subset
    intro z hz
    simp only [mem_support, ne_eq, Int.cast_eq_zero] at hz
    exact hmemρ z hz
  have hRHS : D.logCounting r
      = (∑ z ∈ t, (D.toClosedBall r z : ℝ) * Real.log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * Real.log r := by
    simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    congr 1
    apply finsum_eq_sum_of_support_subset
    intro z hz
    simp only [mem_support, ne_eq] at hz
    apply hmem
    intro h
    simp [h] at hz
  rw [hLHS, hRHS, Finset.sum_mul]
  -- Compare the sums term by term
  have key : ∀ z ∈ t, (D.toClosedBall ρ z : ℝ) * Real.log (r / ρ)
      ≤ (D.toClosedBall r z : ℝ) * Real.log (r * ‖z‖⁻¹)
        + (if z = 0 then (D 0 : ℝ) * Real.log r else 0) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      rw [ite_eq_left rfl, toClosedBall_eval_within _ (by simp),
        toClosedBall_eval_within _ (by simp)]
      simp only [norm_zero, inv_zero, mul_zero, log_zero, mul_zero, zero_add]
      apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hD' 0)
      apply Real.log_le_log (by positivity)
      exact div_le_self hr₀.le hρ
    · rw [ite_eq_right hz0, add_zero]
      by_cases hzρ : z ∈ closedBall (0 : ℂ) |ρ|
      · have hz_norm : ‖z‖ ≤ ρ := by rwa [mem_closedBall_zero_iff, habsρ] at hzρ
        have hz_pos : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz0
        rw [toClosedBall_eval_within _ hzρ, toClosedBall_eval_within _ (by
          rw [mem_closedBall_zero_iff, habsr]
          exact hz_norm.trans hρr.le)]
        apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hD' z)
        rw [div_eq_mul_inv]
        apply Real.log_le_log (by positivity)
        gcongr
      · rw [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzρ, Int.cast_zero, zero_mul]
        by_cases hzr : D.toClosedBall r z = 0
        · simp [hzr]
        · apply mul_nonneg (by exact_mod_cast hpos r z)
          have hz_le : ‖z‖ ≤ r := by
            have := toClosedBall_support_subset_closedBall (r := r) D (mem_support.2 hzr)
            rwa [mem_closedBall_zero_iff, habsr] at this
          apply Real.log_nonneg
          rw [← div_eq_mul_inv, le_div_iff₀ (norm_pos_iff.2 hz0)]
          simpa using hz_le
  calc ∑ z ∈ t, (D.toClosedBall ρ z : ℝ) * Real.log (r / ρ)
      ≤ ∑ z ∈ t, ((D.toClosedBall r z : ℝ) * Real.log (r * ‖z‖⁻¹)
          + (if z = 0 then (D 0 : ℝ) * Real.log r else 0)) := Finset.sum_le_sum key
    _ = (∑ z ∈ t, (D.toClosedBall r z : ℝ) * Real.log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * Real.log r := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' t 0 (fun _ ↦ (D 0 : ℝ) * Real.log r),
          ite_eq_left (Finset.mem_insert_self 0 hfin.toFinset)]

end Function.locallyFinsuppWithin
