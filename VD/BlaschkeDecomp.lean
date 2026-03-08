/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import VD.MathlibSubmitted.Blaschke

@[expose] public section

open Complex ComplexConjugate Filter Metric Set Real


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

theorem meromorphicAt_prod' {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (hf : ∀ i ∈ s, MeromorphicAt (f i) x) :
    MeromorphicAt (∏ i ∈ s, f i) x := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.prod_insert ha]
    apply (hf a (Finset.mem_insert_self a s)).mul
      (hs (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

theorem meromorphicAt_sum' {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (hf : ∀ i ∈ s, MeromorphicAt (f i) x) :
    MeromorphicAt (∑ i ∈ s, f i) x := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.sum_insert ha]
    apply (hf a (Finset.mem_insert_self a s)).add
      (hs (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

/--
The order is additive in products of meromorphic functions.
-/
@[to_fun]
theorem meromorphicOrderAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (hf : ∀ i ∈ s, MeromorphicAt (f i) x) :
    meromorphicOrderAt (∏ i ∈ s, f i) x = ∑ i ∈ s, meromorphicOrderAt (f i) x := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty,
      MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
    simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true]
    apply analyticAt_const.meromorphicNFAt
  | insert a s ha hs =>
    simp_all [Finset.sum_insert ha, Finset.prod_insert ha, meromorphicOrderAt_mul
      (hf a (Finset.mem_insert_self a s))
      (meromorphicAt_prod' (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))]


variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {c w : ℂ}


theorem MeromorphicOn.canonicalDecomposition₀ {f : ℂ → E}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall 0 R), meromorphicOrderAt f u ≠ ⊤) :
    ∃ g : ℂ → E, MeromorphicNFOn g (closedBall 0 R)
      ∧ AnalyticOnNhd ℂ g (ball 0 R)
      ∧ (∀ u : (ball 0 R), g u ≠ 0)
      ∧ f =ᶠ[codiscreteWithin (closedBall 0 R)]
          (∏ᶠ u, (CanonicalFactor R u) ^ (-divisor f (ball 0 R) u)) • g := by
  have η₀ : Set.Finite (-divisor f (ball 0 R)).support := by
    sorry
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
    rw [meromorphicOrderAt_smul]
    rw [meromorphicOrderAt_prod]
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
