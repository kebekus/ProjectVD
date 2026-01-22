import VD.Cartan
import Mathlib

open Asymptotics Filter Function Metric Real Set Classical Topology ValueDistribution

/-
Prove that the proximity function of an analytic function `f` is bounded if and
only if `f` is bounded and hence constant.
-/

namespace ValueDistribution

lemma proximity_congr_codiscrete {f g : ℂ → ℂ} {r : ℝ} (hfg : f =ᶠ[codiscrete ℂ] g) (hr : r ≠ 0) :
    proximity f ⊤ r = proximity g ⊤ r := by
  simp [proximity]
  refine circleAverage_congr_codiscreteWithin ?_ hr

  sorry

end ValueDistribution


namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

lemma proximity_bounded_iff_constant {f : ℂ → ℂ} (h : AnalyticOnNhd ℂ f Set.univ) :
    (EventuallyConst  f (codiscrete ℂ)) ↔ proximity f ⊤ =O[atTop] (1 : ℝ → ℝ) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := eventuallyConst_iff_exists_eventuallyEq.1 h
    rw [isBigO_iff]
    use posLog ‖c‖
    simp




    sorry
  · sorry

end ValueDistribution
