/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
--module

import VD.BoundednessProximity
import VD.Cartan
import VD.MathlibSubmitted.Congruence
import Mathlib

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


lemma characteristic_isBigO_one_iff_constant (h : MeromorphicOn f Set.univ) :
    EventuallyConst f (codiscrete ℂ) ↔ characteristic f ⊤ =O[atTop] (1 : ℝ → ℝ) := by
  constructor
  · intro hf
    apply Asymptotics.IsBigO.add (proximity_bounded_if_eventuallyConstant hf)
    obtain ⟨c, hc⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hf
    simp [logCounting_congr_codiscrete hc, Asymptotics.isBigO_of_le' (c := 0)]
  · intro hf
    unfold characteristic at hf
    have h₁f : proximity f ⊤ =O[atTop] (1 : ℝ → ℝ) := by
      rw [Asymptotics.isBigO_iff] at *
      obtain ⟨c, hc⟩ := hf
      use c
      filter_upwards [hc] with a ha
      simp_all
      sorry
    have h₂f : logCounting f ⊤ =O[atTop] (1 : ℝ → ℝ) := by
      sorry
    sorry

end ValueDistribution
