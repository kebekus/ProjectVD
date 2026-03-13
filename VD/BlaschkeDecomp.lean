/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
--module

import VD.MathlibSubmitted.Blaschke
import VD.MathlibSubmitted.MeromorphicProd

--@[expose] public section

open Complex ComplexConjugate Filter Metric Set Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {c w : ℂ}

theorem zero_canonicalFactor_iff {z : ℂ} (hw : w ∈ ball 0 R) (hz : z ∈ ball 0 R) :
    CanonicalFactor R w z = 0 ↔ z = w := by
  constructor
  · intro h
    by_contra h₁
    have := nonzero_canonicalFactor hw hz h₁
    tauto
  · simp_all

theorem divisor_canonicalFactor (hw : w ∈ ball 0 R) :
    MeromorphicOn.divisor (CanonicalFactor R w) (ball 0 R)
      = -(Function.locallyFinsuppWithin.single w 1).restrict (subset_univ (ball 0 R)) := by
  ext z
  by_cases hz : z ∈ ball 0 R
  · rw [MeromorphicOn.divisor_apply _ hz]
    by_cases h₂z : z = w
    · subst h₂z
      rw [meromorphicOrderAt_canonicalFactor hz]
      have : (-1 : WithTop ℤ).untop₀ = (-1 : ℤ) := by rfl
      simp_all [Function.locallyFinsuppWithin.restrict_apply]
    · have : meromorphicOrderAt (CanonicalFactor R w) z = 0 := by
        rw [(meromorphicNFOn_canonicalFactor hw (mem_univ z)).meromorphicOrderAt_eq_zero_iff]
        exact nonzero_canonicalFactor hw hz h₂z
      simp [this, h₂z, Function.locallyFinsuppWithin.restrict_apply, hz]
    intro z hz
    exact meromorphicOn_canonicalFactor R w z (mem_univ z)
  · simp_all

theorem MeromorphicOn.canonicalDecomposition₀ {f : ℂ → E} :
    MeromorphicNFOn (∏ᶠ u, (CanonicalFactor R u) ^ (-divisor f (ball 0 R) u)) (ball 0 R) := by
  classical
  apply meromorphicNFOn_finprod
  · intro w
    by_cases hw : w ∈ ball 0 R
    · apply MeromorphicNFOn.zpow (fun z _ ↦ (meromorphicNFOn_canonicalFactor hw) (mem_univ z))
    · simp only [hw, not_false_eq_true, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
        neg_zero, zpow_zero]
      apply AnalyticOnNhd.meromorphicNFOn
      apply analyticOnNhd_const
  · intro z hz a ha b hb
    simp_all only [Pi.pow_apply, zpow_neg, inv_eq_zero, mem_setOf_eq]
    have h₁a := eq_zero_of_zpow_eq_zero ha
    have h₂a : a ∈ ball 0 R := by
      have : divisor f (ball 0 R) b ≠ 0 := by aesop
      by_contra h
      simp_all
    have h₁b := eq_zero_of_zpow_eq_zero hb
    have h₂b : b ∈ ball 0 R := by
      have : divisor f (ball 0 R) b ≠ 0 := by aesop
      by_contra h
      simp_all
    rw [zero_canonicalFactor_iff h₂a hz] at h₁a
    rw [zero_canonicalFactor_iff h₂b hz] at h₁b
    simp_all

theorem MeromorphicOn.canonicalDecomposition₁ {f : ℂ → E}
    (h₁f : MeromorphicOn f (closedBall 0 R)) :
    divisor (∏ᶠ u, (CanonicalFactor R u) ^ (-divisor f (ball 0 R) u)) (ball 0 R) = 0 := by
  have η₀ : Set.Finite (-divisor f (ball 0 R)).support := by
    apply Set.Finite.subset (s := (-divisor f (closedBall 0 R)).support)
    · exact (-divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
    · intro z hz
      simp at ⊢ hz
      rw [divisor_apply h₁f]
      rw [divisor_apply] at hz
      assumption
      apply h₁f.mono_set ball_subset_closedBall
      have := (divisor f (ball 0 R)).supportWithinDomain
      aesop
      have := (divisor f (ball 0 R)).supportWithinDomain
      apply ball_subset_closedBall (x := (0 : ℂ)) (ε := R)
      aesop
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
  rw [MeromorphicOn.divisor_prod]
  conv =>
    left
    arg 2
    intro x
    rw [MeromorphicOn.divisor_zpow (fun z hz ↦ meromorphicOn_canonicalFactor R x z (mem_univ z))]
  sorry
  sorry
  sorry

theorem MeromorphicOn.canonicalDecomposition₀₀ {f : ℂ → E}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤) :
    ∃ g : ℂ → E, MeromorphicNFOn g (closedBall 0 R)
      ∧ AnalyticOnNhd ℂ g (ball 0 R)
      ∧ (∀ u : (ball 0 R), g u ≠ 0)
      ∧ f =ᶠ[codiscreteWithin (closedBall 0 R)]
          (∏ᶠ u, (CanonicalFactor R u) ^ (-divisor f (ball 0 R) u)) • g := by
  have η₀ : Set.Finite (-divisor f (ball 0 R)).support := by
    apply Set.Finite.subset (s := (-divisor f (closedBall 0 R)).support)
    · exact (-divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
    · intro z hz
      simp at ⊢ hz
      rw [divisor_apply h₁f]
      rw [divisor_apply] at hz
      assumption
      apply h₁f.mono_set ball_subset_closedBall
      have := (divisor f (ball 0 R)).supportWithinDomain
      aesop
      have := (divisor f (ball 0 R)).supportWithinDomain
      apply ball_subset_closedBall (x := (0 : ℂ)) (ε := R)
      aesop
  have η₁ : (-divisor f (ball 0 R)).support = (divisor f (ball 0 R)).support := by
    aesop
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
  let φ := (∏ i ∈ η₀.toFinset, CanonicalFactor R i ^ (divisor f (ball 0 R)) i) • f
  have hφ : MeromorphicOn φ (closedBall 0 R) := by
    unfold φ
    apply MeromorphicOn.smul _ h₁f
    apply MeromorphicOn.prod
    intro σ
    apply MeromorphicOn.zpow
    intro z₁ hz₁
    apply meromorphicOn_canonicalFactor _ _ _ (mem_univ z₁)
  let g := toMeromorphicNFOn φ (closedBall 0 R)
  have h₁g := meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
  have h₂g : ∀ z ∈ ball 0 R, meromorphicOrderAt g z = 0 := by
    intro z h₁z
    rw [meromorphicOrderAt_toMeromorphicNFOn hφ (ball_subset_closedBall h₁z)]
    unfold φ
    rw [meromorphicOrderAt_smul, meromorphicOrderAt_prod]
    simp_rw [meromorphicOrderAt_zpow (meromorphicOn_canonicalFactor R _ z (mem_univ z))]
    by_cases h₂z : z ∈ (-divisor f (ball 0 R)).support
    ·
      sorry
    · have : MeromorphicOn f (ball 0 R) := by
        sorry
      rw [Finset.sum_eq_zero]
      simp
      rw [η₁] at h₂z
      simp at h₂z
      have := h₂f ⟨z, ball_subset_closedBall h₁z⟩
      simp_all
      intro x hx
      simp_all
      sorry
    sorry
    sorry
    sorry
  use g, h₁g
  constructor
  · intro z hz
    rw [← MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt
      (h₁g (ball_subset_closedBall hz))]
    rw [meromorphicOrderAt_toMeromorphicNFOn hφ (ball_subset_closedBall hz)]
    unfold φ
    rw [meromorphicOrderAt_smul]
    rw [meromorphicOrderAt_prod]
    sorry
    sorry
    sorry
    sorry

  · constructor
    · sorry
    · sorry


theorem MeromorphicOn.canonicalDecomposition {f : ℂ → E}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall 0 R), meromorphicOrderAt f u ≠ ⊤) :
    ∃ g : ℂ → E, AnalyticOnNhd ℂ g (closedBall 0 R) ∧ (∀ u : (closedBall 0 R), g u ≠ 0) ∧
      f =ᶠ[codiscreteWithin (closedBall 0 R)]
        (∏ᶠ u, (· - u) ^ divisor f (sphere 0 R) u)
          • (∏ᶠ u, (CanonicalFactor R u) ^ (-divisor f (ball 0 R) u)) • g := by
  sorry
