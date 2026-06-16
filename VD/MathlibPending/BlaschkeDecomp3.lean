/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.JensenFormula
import VD.MathlibSubmitted.BlaschkeDecomp2

/-!
# Additional Material on the Extended Canonical Decomposition

This file provides companion lemmas to the extended canonical decomposition,
expressing the function `h` (and `log ‖h‖`) entirely in terms of `f`, including
the case where `f` has order zero.
-/

open Complex Filter Function MeromorphicOn Metric Real Set Topology --ValueDistribution

@[fun_prop]
lemma meromorphicAt_canonicalFactor {R : ℝ} {x w : ℂ} : MeromorphicAt (canonicalFactor R w) x := by
  rw [canonicalFactor_def]
  fun_prop

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U V : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Formula goes here
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {x c w : ℂ} {f h : ℂ → E}

/--
Companion lemma to
`congr_codiscreteWitin_closedBall_prod_canonicalFactor_mul_prod_smul`: In the
setting of the extended canonical decomposition, write the function `h` entirely
in terms of `f`.
-/
lemma _root_.ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt
    {f h : ℂ → E} (D : ECanonicalDecomp f h R) (hw : w ∈ closedBall 0 R) (hR : 0 < R) :
    h w
      = ((∏ᶠ i, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f (ball 0 R) i))
          * (∏ᶠ i, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f (sphere 0 R)) i))
          • meromorphicTrailingCoeffAt f w := by
  -- Finiteness properties and side results used throughout the proof
  have h₃f : (divisor f (sphere 0 R)).support.Finite := divisor_sphere_support_finite
  have h₄f : (divisor f (ball 0 R)).support.Finite := D.meromorphicOn.divisor_ball_support_finite
  have := (D.analyticOnNhd w hw).meromorphicAt
  -- Proof body: Substitute `f` using `h₁f` and compute
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
    ((D.meromorphicOn w hw).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (by fun_prop) hw _ D.eventuallyEq),
    finprod_eq_prod_of_mulSupport_subset (s := h₄f.toFinset) _ (by aesop),
    finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _ (by aesop),
    finprod_eq_prod_of_mulSupport_subset (s := h₄f.toFinset) _ (by aesop),
    finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _ (by aesop),
    MeromorphicAt.meromorphicTrailingCoeffAt_smul (by fun_prop)
      (D.analyticOnNhd w hw).meromorphicAt,
    MeromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop) (by fun_prop),
    meromorphicTrailingCoeffAt_prod (by fun_prop), meromorphicTrailingCoeffAt_prod (by fun_prop),
    (D.analyticOnNhd w hw).meromorphicTrailingCoeffAt_of_ne_zero (D.ne_zero w hw), smul_smul,
    mul_mul_mul_comm,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Finset.prod_eq_one, Finset.prod_eq_one,
    mul_one, one_smul]
  · intro x hx
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop), ← zpow_add₀,
      locallyFinsuppWithin.coe_neg, Pi.neg_apply, neg_add_cancel, zpow_zero]
    rw [meromorphicTrailingCoeffAt_id_sub_const]
    grind
  · intro x hx
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop), ← zpow_add₀, add_neg_cancel,
      zpow_zero]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (by fun_prop)
      (meromorphicOrderAt_canonicalFactor_ne_top x hR)
  · rw [← closure_ball _ hR.ne']
    exact isOpen_ball.perfect_closure.2

/--
Companion lemma to
`congr_codiscreteWitin_closedBall_prod_canonicalFactor_mul_prod_smul`: In the
setting of the extended canonical decomposition, write the function `h` entirely
in terms of `f`, under the assumption that `f` has order zero.
-/
lemma _root_.ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt'
    {f h : ℂ → E} (D : ECanonicalDecomp f h R) (h₁w : w ∈ closedBall 0 R)
    (h₂w : meromorphicOrderAt f w = 0) (hR : 0 < R) :
    h w = ((∏ᶠ i, (canonicalFactor R i w) ^ (divisor f (ball 0 R) i))
          * (∏ᶠ i, (w - i) ^ (-divisor f (sphere 0 R)) i))
          • meromorphicTrailingCoeffAt f w := by
  rw [D.eq_smul_meromorphicTrailingCoeffAt h₁w hR]
  congr
  · ext x
    by_cases h₃x : (divisor f (ball 0 R)) x = 0
    · simp [h₃x]
    have h₁x : x ∈ ball 0 R := (divisor f (ball 0 R)).supportWithinDomain h₃x
    have h₂x : w ≠ x := by
      rintro rfl
      exact h₃x (by simp [(D.meromorphicOn.mono_set ball_subset_closedBall).divisor_apply h₁x, h₂w])
    rw [AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero
      (Complex.analyticOnNhd_canonicalFactor R x w h₂x)
      (Complex.canonicalFactor_ne_zero h₁x h₁w h₂x)]
  · ext x
    by_cases h : x = w
    · simp_all [meromorphicTrailingCoeffAt_id_sub_const, divisor_def]
    grind [meromorphicTrailingCoeffAt_id_sub_const]

/--
Companion lemma to
`congr_codiscreteWitin_closedBall_prod_canonicalFactor_mul_prod_smul`: In the
setting of the extended canonical decomposition, write the function `log ‖h‖`
entirely in terms of `f`, under the assumption that `f` has order zero.
-/
lemma _root_.ECanonicalDecomp.log_norm_eq
    {f h : ℂ → E} (D : ECanonicalDecomp f h R) (h₁w : w ∈ closedBall 0 R)
    (h₂w : meromorphicOrderAt f w = 0)
    (hR : 0 < R) :
    Real.log ‖h w‖ = ((∑ᶠ i, (divisor f (ball 0 R) i) * Real.log ‖canonicalFactor R i w‖)
          - (∑ᶠ i, (divisor f (sphere 0 R) i) * Real.log ‖w - i‖))
          + Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
  have h₃f : (divisor f (sphere 0 R)).support.Finite := divisor_sphere_support_finite
  have h₄f : (divisor f (ball 0 R)).support.Finite := D.meromorphicOn.divisor_ball_support_finite
  have η₀ : ∀ x ∈ h₃f.toFinset, ‖w - x‖ ^ (-divisor f (sphere 0 R)) x ≠ 0 := by
    intro x hx
    rw [Finite.mem_toFinset] at hx
    refine zpow_ne_zero _ ?_
    rw [norm_ne_zero_iff, sub_ne_zero]
    rintro rfl
    exact hx (by simp [divisor_apply (D.meromorphicOn.mono_set sphere_subset_closedBall)
      ((divisor f (sphere 0 R)).supportWithinDomain hx), h₂w])
  have η₁ : ∀ x ∈ h₄f.toFinset, ‖canonicalFactor R x w‖ ^ (divisor f (ball 0 R)) x ≠ 0 := by
    intro x hx
    rw [Finite.mem_toFinset] at hx
    refine zpow_ne_zero _ ?_
    rw [ne_eq, norm_eq_zero]
    have h₁x : x ∈ ball 0 R := (divisor f (ball 0 R)).supportWithinDomain hx
    refine canonicalFactor_ne_zero h₁x h₁w ?_
    rintro rfl
    exact hx (by simp [divisor_apply (D.meromorphicOn.mono_set ball_subset_closedBall) h₁x, h₂w])
  rw [D.eq_smul_meromorphicTrailingCoeffAt'
    h₁w h₂w hR, finprod_eq_prod_of_mulSupport_subset (s := h₄f.toFinset) _ (by aesop),
    finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _ (by aesop),
    finsum_eq_sum_of_support_subset (s := h₄f.toFinset) _ (fun _ _ ↦ (by aesop)),
    finsum_eq_sum_of_support_subset (s := h₃f.toFinset) _ (fun _ _ ↦ (by aesop)), norm_smul,
    norm_mul, norm_prod, norm_prod]
  simp_rw [norm_zpow]
  rw [Real.log_mul (mul_ne_zero_iff.2 ⟨Finset.prod_ne_zero_iff.2 η₁, Finset.prod_ne_zero_iff.2 η₀⟩),
    Real.log_mul (Finset.prod_ne_zero_iff.2 η₁) (Finset.prod_ne_zero_iff.2 η₀), Real.log_prod η₁,
    Real.log_prod η₀]
  · congr
    · ext i
      exact log_zpow ‖canonicalFactor R i w‖ ((divisor f (ball 0 R)) i)
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [log_zpow ‖w - i‖ ((-divisor f (sphere 0 R)) i)]
      simp
  · rw [ne_eq, norm_eq_zero]
    apply (D.meromorphicOn w h₁w).meromorphicTrailingCoeffAt_ne_zero (by aesop)
