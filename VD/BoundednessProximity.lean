import VD.Cartan
import Mathlib

open Filter Function Metric Real Set Classical Topology ValueDistribution

/-
Prove that the proximity function of an analytic function `f` is bounded if and
only if `f` is bounded and hence constant.
-/

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

lemma proximity_bounded_iff_constant {f : ℂ → ℂ} (h : AnalyticOnNhd ℂ f Set.univ) :
    (∃ c, f =ᶠ[codiscrete ℂ] c) ↔ proximity f ⊤ =O[atTop] (1 : ℝ → ℝ) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h

    sorry
  · sorry

end ValueDistribution
