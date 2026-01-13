import VD.Cartan
import Mathlib

open Function Metric Real Set Classical Topology ValueDistribution

/--
Prove that the proximity function of an analytic function `f` is bounded if and
only if `f` is bounded and hence constant.
-/

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

lemma proximity_bounded_iff_constant {f : ℂ → ℂ} (h : AnalyticOnNhd ℂ f Set.univ) :
    ∃ c, f = c ↔ proximity f ⊤ =O[Filter.atTop] (1 : ℝ → ℝ) := by
  sorry

end ValueDistribution
