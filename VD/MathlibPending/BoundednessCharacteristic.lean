/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Asymptotic
import VD.MathlibPending.ProximityBounded

/-!
# Asymptotic Behavior of the Characteristic Function

If `f` is complex-meromorphic, we show that the characteristic function for the poles of `f` is
asymptotically bounded if and only if `f` is constant.  See Page 170f of [Lang, *Introduction to
Complex Hyperbolic Spaces*][MR886677] for a detailed discussion.

## TODO

Establish the analogous characterization of rational functions, as functions whose logarithmic
counting function big-O of `log`.
-/

open Filter Function Metric Real Set Topology ValueDistribution

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E}

/--
The characteristic function `characteristic f a` is big-O of a function `g` along `atTop` if and
only if both of its summands, the proximity function and the logarithmic counting function, are
big-O of `g`. The non-trivial implication uses that the proximity and logarithmic counting functions
are eventually non-negative.
-/
lemma characteristic_isBigO_iff {g : ℝ → ℝ} {a : WithTop E} :
    characteristic f a =O[atTop] g ↔
      proximity f a =O[atTop] g ∧ logCounting f a =O[atTop] g := by
  constructor
  · intro hf
    unfold characteristic at hf
    simp only [Asymptotics.isBigO_iff, Pi.add_apply, norm_eq_abs] at *
    obtain ⟨c, hc⟩ := hf
    constructor
    all_goals
    · use c
      filter_upwards [hc, (eventually_ge_atTop 1)] with r h₁r h₂
      have : 0 ≤ proximity f a r := proximity_nonneg r
      have : 0 ≤ logCounting f a r := logCounting_nonneg h₂
      grind
  · exact fun h ↦ h.1.add h.2

/--
The proximity function of `f` agrees, eventually along `atTop`, with the proximity function of the
meromorphic normal form `toMeromorphicNFOn f ⊤` of `f`. This holds because `f` and its normal form
agree away from a codiscrete set, and the proximity function only depends on the values of `f` up to
such a set.
-/
lemma proximity_eq_proximity_toMeromorphicNFOn {a : WithTop E} (h : MeromorphicOn f Set.univ) :
    proximity f a =ᶠ[atTop] proximity (toMeromorphicNFOn f ⊤) a := by
  rw [EventuallyEq, eventually_atTop]
  use 1
  intro _ _
  rw [proximity_congr_codiscrete _ (by linarith)]
  exact toMeromorphicNFOn_eqOn_codiscrete h

/--
Characterization of constant meromorphic functions in terms of the growth of their characteristic
function: a function `f` that is meromorphic on all of `ℂ` is eventually constant along the
codiscrete filter if and only if its characteristic function for the value `⊤` (that is, for the
poles of `f`) is bounded, i.e. big-O of the constant function `1` along `atTop`.

See Page 170f of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.
-/
theorem characteristic_isBigO_one_iff_constant {f : ℂ → ℂ} (h : MeromorphicOn f Set.univ) :
    EventuallyConst f (codiscrete ℂ) ↔ characteristic f ⊤ =O[atTop] (1 : ℝ → ℝ) := by
  constructor
  · intro hf
    apply Asymptotics.IsBigO.add (proximity_isBigO_one_of_eventuallyConst hf)
    obtain ⟨c, hc⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hf
    simp [logCounting_congr_codiscrete hc, Asymptotics.isBigO_of_le' (c := 0)]
  · intro hf
    have ⟨hf₁, hf₂⟩ := characteristic_isBigO_iff.1 hf
    rw [logCounting_isBigO_one_iff_analyticOnNhd (meromorphicOn_univ.mp h)] at hf₂
    have : proximity (toMeromorphicNFOn f ⊤) ⊤ =O[atTop] (1 : ℝ → ℝ) := by
      rwa [Asymptotics.isBigO_congr (proximity_eq_proximity_toMeromorphicNFOn h).symm
        (Eq.eventuallyEq rfl)]
    rw [eventuallyConst_iff_exists_eventuallyEq]
    obtain ⟨c, hc⟩ := (proximity_isBigO_one_iff_exists_eq_const hf₂).mp this
    use c
    filter_upwards [toMeromorphicNFOn_eqOn_codiscrete h] using by aesop

end ValueDistribution
