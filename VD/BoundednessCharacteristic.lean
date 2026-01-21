import VD.Cartan
import Mathlib

open Function Metric Real Set Classical Topology ValueDistribution

/-
Prove that the proximity function of an analytic function `f` is bounded if and
only if `f` is bounded and hence constant.
-/

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

lemma characteristic_isBigO_one_iff_constant {f : ℂ → ℂ} (h : MeromorphicOn f Set.univ) :
    ∃ c, f = c ↔ characteristic f ⊤ =O[Filter.atTop] (1 : ℝ → ℝ) := by
  sorry

end ValueDistribution
