/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
--module

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.CanonicalDecomposition
import VD.MathlibSubmitted.LocallyFinsupp

--@[expose] public section

open Complex ComplexConjugate Filter Function Metric Set Real

set_option backward.isDefEq.respectTransparency false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {c w : ℂ}

/-!
## Other Material
-/

theorem nonneg_of_mem_closedBall {z c : ℂ} {R : ℝ} (h : z ∈ closedBall c R) :
    0 ≤ R := (Complex.norm_nonneg (z - c)).trans (mem_closedBall_iff_norm.1 h)

/--
Variant of `exists_meromorphicOrderAt_ne_top_iff_forall`, with membership in
lieu of subtypes.
-/
theorem MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall_mem {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hU : IsConnected U) :
    (∃ u ∈ U, meromorphicOrderAt f u ≠ ⊤) ↔ (∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤) := by
  convert exists_meromorphicOrderAt_ne_top_iff_forall hf hU
  <;> simp

/--
A finprod of functions that do not vanish locally does not vanish locally.
-/
lemma meromorphicOrderAt_finprod_ne_top {z : ℂ} {F : ℂ → ℂ → ℂ}
    (h₁ : ∀ c, MeromorphicAt (F c) z) (h₂ : ∀ c, meromorphicOrderAt (F c) z ≠ ⊤) :
    meromorphicOrderAt (∏ᶠ c, F c) z ≠ ⊤ := by
  by_cases hF : F.HasFiniteMulSupport
  · simpa [finprod_eq_prod F hF, meromorphicOrderAt_prod (fun x _ ↦ h₁ x)] using fun x _ ↦ h₂ x
  simp [finprod_of_not_hasFiniteMulSupport hF]

/-!
## Material on the canonical factor
-/

/--
The canonical factor `CanonicalFactor R w` vanishes only at `w`.
-/
theorem zero_canonicalFactor_iff {z : ℂ} (hw : w ∈ ball 0 R) (hz : z ∈ ball 0 R) :
    canonicalFactor R w z = 0 ↔ z = w := by
  constructor
  · intro h
    by_contra h₁
    have := Complex.canonicalFactor_ne_zero hw (ball_subset_closedBall hz) h₁
    tauto
  · simp_all

/--
The divisor of the canonical factor `CanonicalFactor R w` is `-w`.
-/
theorem divisor_canonicalFactor (hw : w ∈ ball 0 R) :
    MeromorphicOn.divisor (canonicalFactor R w) (ball 0 R)
      = -(locallyFinsuppWithin.single w 1).restrict (subset_univ (ball 0 R)) := by
  ext z
  by_cases hz : z ∈ ball 0 R
  · rw [MeromorphicOn.divisor_apply (fun z hz ↦ Complex.meromorphicOn_canonicalFactor R w z (mem_univ z)) hz]
    by_cases h₂z : z = w
    · subst h₂z
      rw [meromorphicOrderAt_canonicalFactor hz]
      have : (-1 : WithTop ℤ).untop₀ = (-1 : ℤ) := by rfl
      simp_all [locallyFinsuppWithin.restrict_apply]
    · have : meromorphicOrderAt (canonicalFactor R w) z = 0 := by
        rw [(meromorphicNFOn_canonicalFactor hw (mem_univ z)).meromorphicOrderAt_eq_zero_iff]
        exact canonicalFactor_ne_zero hw (ball_subset_closedBall hz) h₂z
      simp [this, h₂z, locallyFinsuppWithin.restrict_apply, hz]
  · simp_all

/--
Canonical factors are nowhere locally constant zero.
-/
lemma meromorphicOrderAt_canonicalFactor_ne_top {z : ℂ} {R : ℝ} (w : ℂ) (hR : 0 < R) :
    meromorphicOrderAt (canonicalFactor R w) z ≠ ⊤ := by
  suffices h : ∀ z ∈ univ, meromorphicOrderAt (canonicalFactor R w) z ≠ ⊤ from
    h z (mem_univ z)
  rw [← (meromorphicOn_canonicalFactor R w).exists_meromorphicOrderAt_ne_top_iff_forall_mem
    isConnected_univ]
  use 0, mem_univ 0
  by_cases hw : w = 0
  · simp_all [meromorphicOrderAt_canonicalFactor (mem_ball_self hR)]
  have : meromorphicOrderAt (canonicalFactor R w) 0 = 0 := by
    rw [MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
    · simp_all [canonicalFactor, ne_of_gt hR]
    · apply AnalyticAt.meromorphicNFAt
      apply analyticOnNhd_canonicalFactor
      grind
  simp_all

/-!
## Material starts here
-/

namespace MeromorphicOn

variable
  {f : ℂ → E}

-- Auxiliary lemma for the proof of the canonical decomposition theorem
private lemma canonicalDecomposition_aux₁ (F : locallyFinsuppWithin (ball 0 R) ℤ) :
    MeromorphicNFOn (∏ᶠ u, (canonicalFactor R u) ^ (F u)) (ball 0 R) := by
  classical
  apply meromorphicNFOn_finprod
  · intro w
    by_cases hw : w ∈ ball 0 R
    · apply MeromorphicNFOn.zpow (fun z _ ↦ (meromorphicNFOn_canonicalFactor hw) (mem_univ z))
    · simp only [hw, not_false_eq_true, locallyFinsuppWithin.apply_eq_zero_of_notMem,
        zpow_zero]
      apply AnalyticOnNhd.meromorphicNFOn
      apply analyticOnNhd_const
  · intro z hz a ha b hb
    simp_rw [Pi.pow_apply, mem_setOf_eq] at *
    have h₂a : a ∈ ball 0 R := by
      by_contra
      aesop
    have h₂b : b ∈ ball 0 R := by
      by_contra
      aesop
    grind [eq_zero_of_zpow_eq_zero hb, eq_zero_of_zpow_eq_zero ha,
      zero_canonicalFactor_iff h₂b hz, zero_canonicalFactor_iff h₂a hz]

-- Auxiliary lemma for the proof of the canonical decomposition theorem
private lemma canonicalDecomposition_aux₂ (h₁f : MeromorphicOn f (closedBall 0 R)) :
    divisor (∏ᶠ u, (canonicalFactor R u) ^ (divisor f (ball 0 R) u)) (ball 0 R)
      = -(divisor f (ball 0 R)) := by
  have η₀ : (-divisor f (ball 0 R)).support.Finite := by
    apply ((-divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
    intro z hz
    have := (divisor f (ball 0 R)).supportWithinDomain
    rw [mem_support, locallyFinsuppWithin.coe_neg, Pi.neg_apply, ne_eq,
      neg_eq_zero] at ⊢ hz
    rw [divisor_apply h₁f (ball_subset_closedBall (by aesop))]
    rwa [divisor_apply (h₁f.mono_set ball_subset_closedBall) (by aesop)] at hz
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀, divisor_prod]
  simp_rw [divisor_zpow (fun z hz ↦ meromorphicOn_canonicalFactor R _ z (mem_univ z))]
  conv =>
    right
    rw [← locallyFinsuppWithin.sum_apply_smul_single_eq_self η₀]
  apply Finset.sum_congr rfl
  intro x hx
  rw [divisor_canonicalFactor, smul_neg, locallyFinsuppWithin.coe_neg, Pi.neg_apply, neg_smul]
  by_contra
  simp_all
  · intro z hz
    apply zpow (fun x hx ↦ meromorphicOn_canonicalFactor R z x (mem_univ x))
  · intro z hz x hx
    rw [meromorphicOrderAt_zpow (meromorphicOn_canonicalFactor R z x (mem_univ x))]
    lift (meromorphicOrderAt (canonicalFactor R z) x) to ℤ using
      (meromorphicOrderAt_canonicalFactor_ne_top z (pos_of_mem_ball hx)) with ℓ
    simp [← WithTop.coe_mul]

-- Auxiliary lemma for the proof of the canonical decomposition theorem
private lemma canonicalDecomposition_aux₃ {z : ℂ} (hR : 0 < R) :
    meromorphicOrderAt
      (∏ᶠ (c : ℂ), canonicalFactor R c ^ (divisor f (ball 0 R)) c) z ≠ ⊤ := by
  apply meromorphicOrderAt_finprod_ne_top
    (fun _ ↦ MeromorphicAt.zpow (meromorphicOn_canonicalFactor _ _ _ (mem_univ z)) _)
  intro c
  rw [meromorphicOrderAt_zpow (meromorphicOn_canonicalFactor R c z (mem_univ z))]
  lift meromorphicOrderAt (canonicalFactor R c) z to ℤ using
    (meromorphicOrderAt_canonicalFactor_ne_top c hR) with ℓ
  simp [← WithTop.coe_mul]

/--
**Canonical decomposition:** A meromorphic function on a disk is equal, up to
modification over a discrete set, to a product of canonical factors and a
meromorphic function without zeros or poles in the interior of the disk.
-/
theorem canonicalDecomposition
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤) :
    ∃ g : ℂ → E, MeromorphicNFOn g (closedBall 0 R)
      ∧ (∀ u ∈ (ball 0 R), g u ≠ 0)
      ∧ f =ᶠ[codiscreteWithin (closedBall 0 R)]
          (∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u)) • g := by
  by_cases hR : R ≤ 0
  · simp_all [ball_eq_empty.2 hR]
    use fun z ↦ f 0, fun z hz ↦ AnalyticAt.meromorphicNFAt analyticAt_const
    filter_upwards [Filter.self_mem_codiscreteWithin (closedBall 0 R)] with a ha
    have : R = 0 := by grind [nonneg_of_mem_closedBall ha]
    aesop
  rw [not_le] at hR
  have η₀ : (-divisor f (ball 0 R)).support.Finite := by
    have := (divisor f (ball 0 R)).supportWithinDomain
    apply ((-divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
    intro z hz
    simp only [mem_support, locallyFinsuppWithin.coe_neg, Pi.neg_apply, ne_eq,
      neg_eq_zero] at ⊢ hz
    rw [divisor_apply h₁f (ball_subset_closedBall (by aesop))]
    rwa [divisor_apply (h₁f.mono_set ball_subset_closedBall) (by aesop)] at hz
  have η₁ : (-divisor f (ball 0 R)).support = (divisor f (ball 0 R)).support := by aesop
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
  let φ := (∏ᶠ c, canonicalFactor R c ^ (divisor f (ball 0 R)) c) • f
  have hφ : MeromorphicOn φ (closedBall 0 R) := by
    apply smul (MeromorphicOn.finprod _) h₁f
    exact fun z ↦ zpow (fun z₁ hz₁ ↦ meromorphicOn_canonicalFactor _ _ _ (mem_univ z₁)) _
  let g := toMeromorphicNFOn φ (closedBall 0 R)
  have h₁g : MeromorphicNFOn g (closedBall 0 R) :=
    meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
  have h₃g : divisor g (ball 0 R) = 0 := by
    rw [divisor_congr_codiscreteWithin
        ((toMeromorphicNFOn_eqOn_codiscrete hφ).symm.filter_mono
        (codiscreteWithin.mono ball_subset_closedBall)) isOpen_ball,
      divisor_smul _ (fun x hx ↦ h₁f x (ball_subset_closedBall hx))
        (fun z _ ↦ canonicalDecomposition_aux₃ hR)
        (fun z hz ↦ h₂f ⟨z, ball_subset_closedBall hz⟩),
      canonicalDecomposition_aux₂ h₁f, neg_add_cancel]
    apply (canonicalDecomposition_aux₁ _).meromorphicOn
  have h₂g : MeromorphicNFOn g (closedBall 0 R) :=
    meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
  have h₄g : ∀ z ∈ closedBall 0 R, meromorphicOrderAt g z ≠ ⊤ := by
    intro z hz
    rw [meromorphicOrderAt_toMeromorphicNFOn hφ hz, meromorphicOrderAt_smul _ (h₁f z hz)]
    simp only [ne_eq, LinearOrderedAddCommGroupWithTop.add_eq_top, h₂f ⟨z, hz⟩, or_false]
    apply canonicalDecomposition_aux₃ hR
    apply MeromorphicAt.finprod (fun x ↦ (meromorphicOn_canonicalFactor R x z (by tauto)).zpow _)
  use g, h₁g
  constructor
  · intro z hz
    rw [← MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (h₂g (ball_subset_closedBall hz))]
    have : divisor g (ball 0 R) z = 0 := by simp [h₃g]
    rw [divisor_apply (fun x hx ↦ (h₂g (ball_subset_closedBall hx)).meromorphicAt) hz] at this
    simpa [h₄g z (ball_subset_closedBall hz)] using this
  · trans (∏ i ∈ η₀.toFinset, canonicalFactor R i ^ (-(divisor f (ball 0 R)) i)) • φ
    · unfold φ
      rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ _ η₀]
      filter_upwards [Filter.codiscreteWithin.mono (by tauto) η₀.compl_mem_codiscrete,
        Filter.self_mem_codiscreteWithin (closedBall 0 R)] with a ha h₂a
      simp only [Pi.smul_apply', Finset.prod_apply, Pi.pow_apply]
      rw [← smul_assoc, ← Finset.prod_smul, Finset.prod_eq_one, one_smul]
      · intro x hx
        rw [smul_eq_mul, ← zpow_add', neg_add_cancel, zpow_zero]
        simp_all only [ne_eq, Subtype.forall, mem_closedBall, dist_zero_right, mem_compl_iff,
          mem_support, Decidable.not_not, Finite.mem_toFinset, neg_add_cancel,
          not_true_eq_false, neg_eq_zero, and_self, or_self, or_false]
        apply canonicalFactor_ne_zero
        · by_contra h
          simp_all
        · simp_all
        grind
      · intro
        contrapose
        intro
        simp_all
    · filter_upwards [toMeromorphicNFOn_eqOn_codiscrete hφ] with z hz
      simp_all [g]

theorem meromorphicNFAt_comp_iff_of_deriv_ne_zero {x : ℂ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g x) (hg' : deriv g x ≠ 0) :
    MeromorphicNFAt (f ∘ g) x ↔ MeromorphicNFAt f (g x) := by
  simp [meromorphicNFAt_iff_analyticAt_or, analyticAt_comp_iff_of_deriv_ne_zero hg hg',
    meromorphicAt_comp_iff_of_deriv_ne_zero hg hg',
    meromorphicOrderAt_comp_of_deriv_ne_zero hg hg']

end MeromorphicOn
