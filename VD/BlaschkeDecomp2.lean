/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
--module

import VD.MathlibSubmitted.BlaschkeDecomp
import VD.MathlibSubmitted.Perfect

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
  by_cases h₂ : Set.Finite f.mulSupport
  · grind [finprod_eq_prod f h₂, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

theorem finprod_apply_ne_zero {ι : Type*} {N₀ M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀] [NoZeroDivisors M₀] {n : N₀}
  {f : ι → N₀ → M₀} (h : ∀ i, f i n ≠ 0) :
    (∏ᶠ i, f i) n ≠ 0 := by
  by_cases h₂ : Set.Finite f.mulSupport
  · rw [finprod_eq_prod f h₂]
    grind [Finset.prod_apply, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

/-!
# Terms in the Canonical Decomposition
-/

theorem canonicalDecomposition₀ {f g : ℂ → E}
    (hR : 0 < R)
    (h₁g : MeromorphicNFOn g (closedBall 0 R))
    (h₃g: f =ᶠ[codiscreteWithin (closedBall 0 R)] (∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u)) • g) :
    AnalyticOnNhd ℂ (∏ᶠ (u : ℂ), canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) (sphere 0 R) := by
  intro x hx
  apply analyticAt_finprod
  intro a
  by_cases ha : a ∈ ball 0 R
  · apply (analyticOnNhd_canonicalFactor R a x (by aesop)).zpow
      (canonicalFactor_ne_zero ha (by aesop) (by aesop))
  · simp_all
    apply analyticAt_const

theorem canonicalDecomposition₁ {f g : ℂ → E}
    (hR : 0 < R)
    (hx : x ∈ sphere 0 R)
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₁g : MeromorphicNFOn g (closedBall 0 R))
    (h₃g: f =ᶠ[codiscreteWithin (closedBall 0 R)] (∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u)) • g) :
    f =ᶠ[𝓝[≠] x] (∏ᶠ (u : ℂ), canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) • g := by
  apply MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect (U := closedBall 0 R)
    (h₁f x (by aesop)) ((canonicalDecomposition₀ hR h₁g h₃g x hx).meromorphicAt.smul
      (h₁g.meromorphicOn x (by aesop))) (by aesop) _ h₃g
  rw [← closure_ball 0 hR.ne']
  apply PerfectSpace.preperfect_closure_of_isOpen isOpen_ball

theorem canonicalDecomposition₂ {f g : ℂ → E}
    (hR : 0 < R)
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₁g : MeromorphicNFOn g (closedBall 0 R))
    (h₂g : ∀ u ∈ (ball 0 R), g u ≠ 0)
    (h₃g: f =ᶠ[codiscreteWithin (closedBall 0 R)] (∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u)) • g) :
    divisor g (closedBall 0 R) x = divisor f (sphere 0 R) x := by
  rcases lt_trichotomy ‖x‖ R with h|h|h
  · have : x ∉ sphere (0 : ℂ) R := by aesop
    have := (h₁g (mem_closedBall_zero_iff.mpr h.le)).meromorphicOrderAt_eq_zero_iff.2 (h₂g x (by aesop))
    rw [divisor_apply h₁g.meromorphicOn (mem_closedBall_zero_iff.mpr h.le)]
    simp_all
  · have η₁ : AnalyticAt ℂ (∏ᶠ (u : ℂ), canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x := by
      apply analyticAt_finprod
      intro a
      by_cases ha : a ∈ ball 0 R
      · apply AnalyticAt.zpow
        · apply analyticOnNhd_canonicalFactor
          aesop
        · apply canonicalFactor_ne_zero ha (by aesop)
          aesop
      · simp_all
        apply analyticAt_const
    have η₀ : f =ᶠ[𝓝[≠] x] (∏ᶠ (u : ℂ), canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) • g := by
      apply MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect (U := closedBall 0 R)
        (h₁f x (by aesop)) (η₁.meromorphicAt.smul (h₁g.meromorphicOn x (by aesop))) (by aesop) _ h₃g
      rw [← closure_ball 0 hR.ne']
      apply PerfectSpace.preperfect_closure_of_isOpen isOpen_ball
    have : meromorphicOrderAt (∏ᶠ (u : ℂ), canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x = 0 := by
      rw [MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
      apply finprod_apply_ne_zero
      intro a
      by_cases ha : a ∈ ball 0 R
      · apply zpow_ne_zero
        apply canonicalFactor_ne_zero ha (by aesop)
        aesop
      · simp_all
      apply η₁.meromorphicNFAt
    rw [divisor_apply (h₁f.mono_set sphere_subset_closedBall) (by aesop),
      divisor_apply h₁g.meromorphicOn (by aesop), meromorphicOrderAt_congr η₀,
      meromorphicOrderAt_smul η₁.meromorphicAt (h₁g (by aesop)).meromorphicAt]
    simp_all
  · have : x ∉ sphere (0 : ℂ) R := by aesop
    simp_all

end MeromorphicOn
