/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
--module

import VD.BoundednessProximity
import VD.MathlibSubmitted.Congruence
import VD.MathlibPending.BoundednessLogCounting

open Filter Function Metric Real Set Classical Topology ValueDistribution

/-!
# Asymptotic Behavior of the Characteristic Function

If `f` is complex-meromorphic, we show that the characteristic function for the
poles of `f` is asymptotically bounded if and only if `f` is constant.  See Page
170f of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a
detailed discussion.

## TODO

Establish the analogous characterization of rational functions, as functions
whose logarithmic counting function big-O of `log`.
-/

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E}

lemma characteristic_isBigO_iff {g : ℝ → ℝ} {a : WithTop E} :
    characteristic f a =O[atTop] g ↔ proximity f a =O[atTop] g ∧ logCounting f a =O[atTop] g := by
  constructor
  · intro hf
    unfold characteristic at hf
    simp only [Asymptotics.isBigO_iff, Pi.add_apply, norm_eq_abs] at *
    obtain ⟨c, hc⟩ := hf
    constructor
    all_goals
    · use c
      filter_upwards [hc, (eventually_ge_atTop 1)] with r h₁r h₂
      have σ₁ : 0 ≤ proximity f a r := proximity_nonneg r
      have σ₂ : 0 ≤ logCounting f a r := logCounting_nonneg h₂
      trans |proximity f a r + logCounting f a r|
      · linarith [abs_of_nonneg σ₁, abs_of_nonneg σ₂, abs_of_nonneg (add_nonneg σ₁ σ₂)]
      · exact h₁r
  · exact fun h ↦ h.1.add h.2

lemma proximity_eq_proximity_toMeromorphiNFOn {a : WithTop E} (h : MeromorphicOn f Set.univ) :
    proximity f a =ᶠ[atTop] proximity (toMeromorphicNFOn f ⊤) a := by
  rw [EventuallyEq, eventually_atTop]
  use 1
  intro _ _
  rw [proximity_congr_codiscrete _ (by linarith)]
  exact toMeromorphicNFOn_eqOn_codiscrete h

lemma characteristic_isBigO_one_iff_constant (h : MeromorphicOn f Set.univ) :
    EventuallyConst f (codiscrete ℂ) ↔ characteristic f ⊤ =O[atTop] (1 : ℝ → ℝ) := by
  constructor
  · intro hf
    apply Asymptotics.IsBigO.add (proximity_bounded_if_eventuallyConstant hf)
    obtain ⟨c, hc⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hf
    simp [logCounting_congr_codiscrete hc, Asymptotics.isBigO_of_le' (c := 0)]
  · intro hf
    have ⟨hf₁, hf₂⟩ := characteristic_isBigO_iff.1 hf
    rw [logCounting_isBigO_one_iff_analyticOnNhd (meromorphicOn_univ.mp h)] at hf₂
    have : proximity (toMeromorphicNFOn f ⊤) ⊤ =O[atTop] (1 : ℝ → ℝ) := by
      rwa [Asymptotics.isBigO_congr (proximity_eq_proximity_toMeromorphiNFOn h).symm
        (Eq.eventuallyEq rfl)]
    rw [eventuallyConst_iff_exists_eventuallyEq]
    obtain ⟨c, hc⟩ := (proximity_bounded_iff_constant hf₂).2 this
    use c
    filter_upwards [toMeromorphicNFOn_eqOn_codiscrete h] using by aesop

end ValueDistribution
