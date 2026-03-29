/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
--module

import VD.MathlibPending.BlaschkeDecomp

open Complex ComplexConjugate Filter Function Metric Set Topology Real

set_option backward.isDefEq.respectTransparency false


/-!
## Material starts here
-/

namespace MeromorphicOn


variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {x c w : ℂ}

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

theorem canonicalDecomposition₂ {f g : ℂ → E}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤)
    (h₁g : MeromorphicNFOn g (closedBall 0 R))
    (h₂g : ∀ u ∈ (ball 0 R), g u ≠ 0)
    (h₃g: f =ᶠ[codiscreteWithin (closedBall 0 R)] (∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u)) • g) :
    divisor g (closedBall 0 R) x = divisor f (sphere 0 R) x := by
  rcases lt_trichotomy ‖x‖ R with h|h|h
  · have : x ∉ sphere (0 : ℂ) R := by aesop
    have := (h₁g (mem_closedBall_zero_iff.mpr h.le)).meromorphicOrderAt_eq_zero_iff.2 (h₂g x (by aesop))
    rw [divisor_apply h₁g.meromorphicOn (mem_closedBall_zero_iff.mpr h.le)]
    simp_all
  · have η₀ : f =ᶠ[𝓝[≠] x] (∏ᶠ (u : ℂ), canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) • g := by
      rw [← MeromorphicAt.frequently_eq_iff_eventuallyEq]

      sorry
    have η₁ : AnalyticAt ℂ (∏ᶠ (u : ℂ), canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x := by
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
    have : meromorphicOrderAt f x = meromorphicOrderAt g x := by
      rw [meromorphicOrderAt_congr η₀]
      rw [meromorphicOrderAt_smul]
      simp_all
      apply η₁.meromorphicAt
      apply (h₁g _).meromorphicAt
      aesop
    rw [divisor_apply, divisor_apply]
    simp_all
    -- MeromorphicOn f (sphere 0 R)
    intro x hx
    apply h₁f x (sphere_subset_closedBall hx)
    -- x ∈ sphere 0 R
    aesop
    -- MeromorphicOn g (closedBall 0 R)
    exact h₁g.meromorphicOn
    -- x ∈ closedBall 0 R
    aesop
  · have : x ∉ sphere (0 : ℂ) R := by aesop
    simp_all

end MeromorphicOn
