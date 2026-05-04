/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
--module

import Mathlib.Analysis.Normed.Module.Connected
import VD.MathlibSubmitted.BlaschkeDecomp

open Complex ComplexConjugate Filter Function Metric Set Topology Real

set_option backward.isDefEq.respectTransparency false

/-!
## Material starts here
-/

namespace MeromorphicOn


variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {x c w : ℂ}

/-!
# Generic Material
-/

theorem finprod_ne_zero {ι : Type*} {M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
  {f : ι → M₀} (h : ∀ i, f i ≠ 0) :
    ∏ᶠ i, f i ≠ 0 := by
  by_cases h₂ : f.mulSupport.Finite
  · grind [finprod_eq_prod f h₂, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

theorem finprod_apply_ne_zero {ι : Type*} {N₀ M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀] [NoZeroDivisors M₀] {n : N₀}
  {f : ι → N₀ → M₀} (h : ∀ i, f i n ≠ 0) :
    (∏ᶠ i, f i) n ≠ 0 := by
  by_cases h₂ : f.mulSupport.Finite
  · rw [finprod_eq_prod f h₂]
    grind [Finset.prod_apply, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

@[simp] theorem mem_codiscreteWithin_subsingleton {X : Type*} [TopologicalSpace X] [T1Space X]
    {s t : Set X} (h : Set.Subsingleton t) :
    s ∈ codiscreteWithin t := by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  intro z hz
  use univ \ t, nhdsNE_of_nhdsNE_sdiff_finite univ_mem h.finite, by aesop

/-!
# Terms in the Canonical Decomposition
-/

/--
In the setting of `congr_codiscreteWitin_closedBall_prod_canonicalFactor_smul`,
the function associated with the divisor of `g` is the divisor of `f`, seen as a
meromorphic function on the sphere.
-/
theorem divisor_congr_codiscreteWitin_closedBall_prod_canonicalFactor_smul {f g : ℂ → E}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₁g : MeromorphicNFOn g (closedBall 0 R))
    (h₂g : ∀ u ∈ (ball 0 R), g u ≠ 0)
    (h₃g: f =ᶠ[codiscreteWithin (closedBall 0 R)] (∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u)) • g)
    (hR : 0 < R) :
    divisor g (closedBall 0 R) x = divisor f (sphere 0 R) x := by
  rcases lt_trichotomy ‖x‖ R with h|h|h
  · have : x ∉ sphere (0 : ℂ) R := by aesop
    have := (h₁g (mem_closedBall_zero_iff.mpr h.le)).meromorphicOrderAt_eq_zero_iff.2 (h₂g x (by aesop))
    rw [divisor_apply h₁g.meromorphicOn (mem_closedBall_zero_iff.mpr h.le)]
    simp_all
  · have η₁ : AnalyticAt ℂ (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x := by
      apply analyticAt_finprod
      intro a
      by_cases ha : a ∈ ball 0 R
      · exact AnalyticAt.zpow (analyticOnNhd_canonicalFactor _ _ _ (by aesop))
          (canonicalFactor_ne_zero ha (by aesop) (by aesop))
      · simp_all only [mem_ball, dist_zero_right, ne_eq, zpow_neg, not_lt,
          locallyFinsuppWithin.apply_eq_zero_of_notMem, neg_zero, zpow_zero]
        exact analyticAt_const
    have η₀ : f =ᶠ[𝓝[≠] x] (∏ᶠ (u : ℂ), canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) • g := by
      apply MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect (U := closedBall 0 R)
        (h₁f x (by aesop)) (η₁.meromorphicAt.smul (h₁g.meromorphicOn x (by aesop))) (by aesop) _ h₃g
      rw [← closure_ball 0 hR.ne']
      exact isOpen_ball.perfect_closure.2
    have : meromorphicOrderAt (∏ᶠ (u : ℂ), canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x = 0 := by
      rw [MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff η₁.meromorphicNFAt]
      apply finprod_apply_ne_zero
      intro a
      by_cases ha : a ∈ ball 0 R
      · exact zpow_ne_zero _ (canonicalFactor_ne_zero ha (by aesop) (by aesop))
      · simp_all
    rw [divisor_apply (h₁f.mono_set sphere_subset_closedBall) (by aesop),
      divisor_apply h₁g.meromorphicOn (by aesop), meromorphicOrderAt_congr η₀,
      meromorphicOrderAt_smul η₁.meromorphicAt (h₁g (by aesop)).meromorphicAt]
    simp_all
  · have : x ∉ sphere (0 : ℂ) R := by aesop
    simp_all

/--
**Extended canonical decomposition:** A meromorphic function on a closed disk is
equal, up to modification over a discrete set, to a product of a non-vanishing
analytic function, canonical factors and meromorphic functions of the form `(x -
const) ^ n` where `const` is on the circumference of the disk.
-/
theorem congr_codiscreteWitin_closedBall_prod_canonicalFactor_mul_prod_smul {f : ℂ → E}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤) :
    ∃ h : ℂ → E, AnalyticOnNhd ℂ h (closedBall 0 R)
      ∧ (∀ u ∈ (closedBall 0 R), h u ≠ 0)
      ∧ f =ᶠ[codiscreteWithin (closedBall 0 R)]
          ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
            * (∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h := by
  rcases gt_trichotomy 0 R with hR | hR | hR
  · simp_all
    use fun _ ↦ f 0
    filter_upwards [Filter.self_mem_codiscreteWithin ∅] with a ha
    tauto
  · have he : meromorphicTrailingCoeffAt f 0 ≠ 0 := by
      apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (h₁f 0 _) _
      <;> simp_all
    simp_all
    use fun _ ↦ meromorphicTrailingCoeffAt f 0, fun _ _ ↦ by fun_prop
    simp only [hR.symm, norm_le_zero_iff, he, not_false_eq_true, implies_true, closedBall_zero,
      ball_zero, mem_empty_iff_false, locallyFinsuppWithin.apply_eq_zero_of_notMem, zpow_zero,
      inv_one, finprod_one, one_mul, true_and]
    apply mem_codiscreteWithin_subsingleton subsingleton_singleton
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := congr_codiscreteWitin_closedBall_prod_canonicalFactor_smul h₁f h₂f
  have h₄g : ∀ (u : ↑(closedBall (0 : ℂ) R)), meromorphicOrderAt g ↑u ≠ ⊤ := by
    rw [← h₁g.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
      (isConnected_closedBall hR.le)]
    have s₀ : (0 : ℂ) ∈ ball 0 R := by simp [hR]
    have s₁ : (0 : ℂ) ∈ closedBall 0 R := by simp [hR.le]
    use ⟨0, s₁⟩
    rw [(h₁g s₁).meromorphicOrderAt_eq_zero_iff.2 (h₂g 0 s₀)]
    simp only [ne_eq, LinearOrderedAddCommGroupWithTop.zero_ne_top, not_false_eq_true]
  obtain ⟨h, h₁h, h₂h, h₃h⟩ := h₁g.meromorphicOn.extract_zeros_poles h₄g
    ((divisor g (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R))
  use h, h₁h, (h₂h ⟨·, ·⟩)
  filter_upwards [h₃g, h₃h] with a h₁a h₂a
  simp_rw [← divisor_congr_codiscreteWitin_closedBall_prod_canonicalFactor_smul h₁f h₁g h₂g h₃g hR]
  simp_all [← smul_assoc]

end MeromorphicOn
