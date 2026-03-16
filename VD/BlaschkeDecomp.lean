/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
--module

import Mathlib.Analysis.Normed.Module.Connected
import VD.MathlibSubmitted.Blaschke
import VD.MathlibSubmitted.MeromorphicProd
import VD.MathlibSubmitted.LocallyFinsupp

--@[expose] public section

open Complex ComplexConjugate Filter Metric Set Real

set_option backward.isDefEq.respectTransparency false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {c w : ℂ}

/-!
## Other Material
-/

theorem nonneg_of_mem_closedBall {z c : ℂ} {R : ℝ} (h : z ∈ closedBall c R) :
    0 ≤ R := by
  rw [mem_closedBall_iff_norm] at h
  trans ‖z - c‖
  · exact Complex.norm_nonneg (z - c)
  · exact h

theorem MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall_mem {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hU : IsConnected U) :
    (∃ u ∈ U, meromorphicOrderAt f u ≠ ⊤) ↔ (∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤) := by
  convert exists_meromorphicOrderAt_ne_top_iff_forall hf hU
  <;> simp

lemma meromorphicOrderAt_finprod_ne_top {z : ℂ} {F : ℂ → ℂ → ℂ}
    (h₁ : ∀ c, MeromorphicAt (F c) z) (h₂ : ∀ c, meromorphicOrderAt (F c) z ≠ ⊤) :
    meromorphicOrderAt (∏ᶠ c, F c) z ≠ ⊤ := by
  by_cases hF : Function.HasFiniteMulSupport F
  · simpa [finprod_eq_prod F hF, meromorphicOrderAt_prod (fun x _ ↦ h₁ x)] using fun x _ ↦ h₂ x
  simp [finprod_of_not_hasFiniteMulSupport hF]

/-!
## Material on the canonical factor
-/
theorem zero_canonicalFactor_iff {z : ℂ} (hw : w ∈ ball 0 R) (hz : z ∈ ball 0 R) :
    CanonicalFactor R w z = 0 ↔ z = w := by
  constructor
  · intro h
    by_contra h₁
    have := canonicalFactor_ne_zero hw (ball_subset_closedBall hz) h₁
    tauto
  · simp_all

theorem divisor_canonicalFactor (hw : w ∈ ball 0 R) :
    MeromorphicOn.divisor (CanonicalFactor R w) (ball 0 R)
      = -(Function.locallyFinsuppWithin.single w 1).restrict (subset_univ (ball 0 R)) := by
  ext z
  by_cases hz : z ∈ ball 0 R
  · rw [MeromorphicOn.divisor_apply (fun z hz ↦ meromorphicOn_canonicalFactor R w z (mem_univ z)) hz]
    by_cases h₂z : z = w
    · subst h₂z
      rw [meromorphicOrderAt_canonicalFactor hz]
      have : (-1 : WithTop ℤ).untop₀ = (-1 : ℤ) := by rfl
      simp_all [Function.locallyFinsuppWithin.restrict_apply]
    · have : meromorphicOrderAt (CanonicalFactor R w) z = 0 := by
        rw [(meromorphicNFOn_canonicalFactor hw (mem_univ z)).meromorphicOrderAt_eq_zero_iff]
        exact canonicalFactor_ne_zero hw (ball_subset_closedBall hz) h₂z
      simp [this, h₂z, Function.locallyFinsuppWithin.restrict_apply, hz]
  · simp_all

lemma meromorphicOrderAt_canonicalFactor_ne_top (R : ℝ) (w : ℂ) (hR : 0 < R) :
    ∀ z, meromorphicOrderAt (CanonicalFactor R w) z ≠ ⊤ := by
  suffices h : ∀ z ∈ univ, meromorphicOrderAt (CanonicalFactor R w) z ≠ ⊤ from
    fun z ↦ h z (mem_univ z)
  rw [← (meromorphicOn_canonicalFactor R w).exists_meromorphicOrderAt_ne_top_iff_forall_mem
    isConnected_univ]
  use 0, mem_univ 0
  by_cases hw : w = 0
  · simp_all [meromorphicOrderAt_canonicalFactor (mem_ball_self hR)]
  have : meromorphicOrderAt (CanonicalFactor R w) 0 = 0 := by
    rw [MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
    · simp_all [CanonicalFactor, ne_of_gt hR]
    · apply AnalyticAt.meromorphicNFAt
      apply analyticOnNhd_canonicalFactor
      grind
  simp_all

/-!
## Material starts here
-/

theorem MeromorphicOn.canonicalDecomposition₀ (F : Function.locallyFinsuppWithin (ball 0 R) ℤ) :
    MeromorphicNFOn (∏ᶠ u, (CanonicalFactor R u) ^ (F u)) (ball 0 R) := by
  classical
  apply meromorphicNFOn_finprod
  · intro w
    by_cases hw : w ∈ ball 0 R
    · apply MeromorphicNFOn.zpow (fun z _ ↦ (meromorphicNFOn_canonicalFactor hw) (mem_univ z))
    · simp only [hw, not_false_eq_true, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
        zpow_zero]
      apply AnalyticOnNhd.meromorphicNFOn
      apply analyticOnNhd_const
  · intro z hz a ha b hb
    simp_all only [Pi.pow_apply, mem_setOf_eq]
    have h₁a := eq_zero_of_zpow_eq_zero ha
    have h₂a : a ∈ ball 0 R := by
      have : F b ≠ 0 := by aesop
      by_contra h
      simp_all
    rw [zero_canonicalFactor_iff h₂a hz] at h₁a
    have h₁b := eq_zero_of_zpow_eq_zero hb
    have h₂b : b ∈ ball 0 R := by
      have : F b ≠ 0 := by aesop
      by_contra h
      simp_all
    rw [zero_canonicalFactor_iff h₂b hz] at h₁b
    aesop

theorem MeromorphicOn.canonicalDecomposition₁ {f : ℂ → E} (h₁f : MeromorphicOn f (closedBall 0 R)) :
    divisor (∏ᶠ u, (CanonicalFactor R u) ^ (divisor f (ball 0 R) u)) (ball 0 R)
      = -(divisor f (ball 0 R)) := by
  have η₀ : Set.Finite (-divisor f (ball 0 R)).support := by
    apply Set.Finite.subset (s := (-divisor f (closedBall 0 R)).support)
    · exact (-divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
    · intro z hz
      have := (divisor f (ball 0 R)).supportWithinDomain
      rw [Function.mem_support, Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, ne_eq,
        neg_eq_zero] at ⊢ hz
      rw [divisor_apply h₁f (ball_subset_closedBall (by aesop))]
      rwa [divisor_apply (h₁f.mono_set ball_subset_closedBall) (by aesop)] at hz
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀, MeromorphicOn.divisor_prod]
  simp_rw [MeromorphicOn.divisor_zpow (fun z hz ↦ meromorphicOn_canonicalFactor R _ z (mem_univ z))]
  conv =>
    right
    rw [← Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self η₀]
  apply Finset.sum_congr rfl
  intro x hx
  rw [divisor_canonicalFactor, smul_neg, Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, neg_smul]
  by_contra
  simp_all
  · intro z hz
    apply MeromorphicOn.zpow (fun x hx ↦ meromorphicOn_canonicalFactor R z x (mem_univ x))
  · intro z hz x hx
    rw [meromorphicOrderAt_zpow (meromorphicOn_canonicalFactor R z x (mem_univ x))]
    lift (meromorphicOrderAt (CanonicalFactor R z) x) to ℤ using
      (meromorphicOrderAt_canonicalFactor_ne_top R z (pos_of_mem_ball hx) x) with ℓ
    simp [← WithTop.coe_mul]

theorem MeromorphicOn.canonicalDecomposition₁₁ {f : ℂ → E} (hR : 0 < R):
    ∀ z, meromorphicOrderAt (∏ᶠ (c : ℂ), CanonicalFactor R c ^ (divisor f (ball 0 R)) c) z ≠ ⊤ := by
  intro z
  apply meromorphicOrderAt_finprod_ne_top
  · intro c
    apply MeromorphicAt.zpow (meromorphicOn_canonicalFactor _ _ _ (mem_univ z))
  · intro c
    rw [meromorphicOrderAt_zpow (meromorphicOn_canonicalFactor R c z (mem_univ z))]
    lift meromorphicOrderAt (CanonicalFactor R c) z to ℤ using
      (meromorphicOrderAt_canonicalFactor_ne_top R c hR z) with ℓ
    rw [← WithTop.coe_mul]
    exact WithTop.coe_ne_top

theorem MeromorphicOn.canonicalDecomposition₀₀ {f : ℂ → E}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤) :
    ∃ g : ℂ → E, MeromorphicNFOn g (closedBall 0 R)
      ∧ AnalyticOnNhd ℂ g (ball 0 R)
      ∧ (∀ u ∈ (ball 0 R), g u ≠ 0)
      ∧ f =ᶠ[codiscreteWithin (closedBall 0 R)]
          (∏ᶠ u, (CanonicalFactor R u) ^ (-divisor f (ball 0 R) u)) • g := by
  by_cases hR : R ≤ 0
  · simp_all [ball_eq_empty.2 hR]
    use fun z ↦ f 0, fun z hz ↦ AnalyticAt.meromorphicNFAt analyticAt_const
    filter_upwards [Filter.self_mem_codiscreteWithin (closedBall 0 R)] with a ha
    have : R = 0 := by grind [nonneg_of_mem_closedBall ha]
    aesop
  rw [not_le] at hR
  have η₀ : Set.Finite (-divisor f (ball 0 R)).support := by
    have := (divisor f (ball 0 R)).supportWithinDomain
    apply Set.Finite.subset ((-divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R))
    intro z hz
    simp only [Function.mem_support, Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, ne_eq,
      neg_eq_zero] at ⊢ hz
    rw [divisor_apply h₁f (ball_subset_closedBall (by aesop))]
    rwa [divisor_apply (h₁f.mono_set ball_subset_closedBall) (by aesop)] at hz
  have η₁ : (-divisor f (ball 0 R)).support = (divisor f (ball 0 R)).support := by aesop
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
  let φ := (∏ᶠ c, CanonicalFactor R c ^ (divisor f (ball 0 R)) c) • f
  have hφ : MeromorphicOn φ (closedBall 0 R) := by
    apply MeromorphicOn.smul (meromorphicOn_finprod _) h₁f
    intro z
    apply MeromorphicOn.zpow
      (fun z₁ hz₁ ↦ meromorphicOn_canonicalFactor _ _ _ (mem_univ z₁))
  let g := toMeromorphicNFOn φ (closedBall 0 R)
  have h₁g : MeromorphicNFOn g (closedBall 0 R) :=
    meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
  have h₃g : divisor g (ball 0 R) = 0 := by
    rw [MeromorphicOn.divisor_congr_codiscreteWithin
        ((toMeromorphicNFOn_eqOn_codiscrete hφ).symm.filter_mono
        (codiscreteWithin.mono ball_subset_closedBall)) isOpen_ball,
      MeromorphicOn.divisor_smul _ (fun x hx ↦ h₁f x (ball_subset_closedBall hx))
        (fun z hz ↦ MeromorphicOn.canonicalDecomposition₁₁ hR z)
        (fun z hz ↦ h₂f ⟨z, ball_subset_closedBall hz⟩),
      MeromorphicOn.canonicalDecomposition₁ h₁f, neg_add_cancel]
    apply (MeromorphicOn.canonicalDecomposition₀ _).meromorphicOn
  have h₂g : MeromorphicNFOn g (closedBall 0 R) :=
    meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
  have h₄g : ∀ z ∈ closedBall 0 R, meromorphicOrderAt g z ≠ ⊤ := by
    intro z hz
    rw [meromorphicOrderAt_toMeromorphicNFOn]
    unfold φ
    rw [meromorphicOrderAt_smul]
    simp only [ne_eq, LinearOrderedAddCommGroupWithTop.add_eq_top, h₂f ⟨z, hz⟩, or_false]
    apply MeromorphicOn.canonicalDecomposition₁₁ hR

    apply meromorphicAt_finprod
    intro x
    apply MeromorphicAt.zpow
    exact meromorphicOn_canonicalFactor _ _ z (mem_univ z)
    exact h₁f z hz
    exact hφ
    exact hz
  use g, h₁g
  constructor
  · intro z hz
    rw [← MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt
      (h₁g (ball_subset_closedBall hz))]
    have : divisor g (ball 0 R) z = 0 := by simp [h₃g]
    rw [divisor_apply, WithTop.untop₀_eq_zero] at this
    rcases this
    <;> simp_all
    intro x hx
    apply (h₂g (ball_subset_closedBall hx)).meromorphicAt
    exact hz
  · constructor
    · intro z hz
      rw [← MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
      have : divisor g (ball 0 R) z = 0 := by simp [h₃g]
      rw [divisor_apply] at this
      have := h₄g z (ball_subset_closedBall hz)
      simp_all
      intro x hx
      apply (h₂g (ball_subset_closedBall hx)).meromorphicAt
      exact hz
      apply (h₂g (ball_subset_closedBall hz))
    · trans (∏ i ∈ η₀.toFinset, CanonicalFactor R i ^ (-(divisor f (ball 0 R)) i)) • φ
      · unfold φ
        rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ _ η₀]
        have : (-divisor f (ball 0 R)).supportᶜ ∈ codiscreteWithin (closedBall 0 R) := by
          have := Set.Finite.compl_mem_codiscrete η₀
          unfold codiscrete at this
          have := Filter.codiscreteWithin.mono (subset_univ (closedBall (0 : ℂ) R))
          apply this
          apply Set.Finite.compl_mem_codiscrete η₀
        filter_upwards [this, Filter.self_mem_codiscreteWithin (closedBall 0 R)] with a ha h₂a
        simp only [Pi.smul_apply', Finset.prod_apply, Pi.pow_apply]
        rw [← smul_assoc]
        rw [← Finset.prod_smul]
        rw [Finset.prod_eq_one]
        simp
        intro x hx
        rw [smul_eq_mul]
        rw [← zpow_add' (a := CanonicalFactor R x a)]
        simp
        simp_all
        apply canonicalFactor_ne_zero
        · by_contra h
          simp_all
        · simp_all
        grind
        · intro i
          contrapose
          simp
          intro hi
          simp_all
      · filter_upwards [toMeromorphicNFOn_eqOn_codiscrete hφ] with z hz
        simp_all [g]
