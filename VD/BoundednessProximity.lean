import VD.Cartan
import Mathlib

open Asymptotics Filter Function Metric Real Set Classical Topology ValueDistribution

/-
Prove that the proximity function of an analytic function `f` is bounded if and
only if `f` is bounded and hence constant.
-/

namespace ValueDistribution

lemma proximity_congr_codiscreteWithin {f g : ℂ → ℂ} {a : WithTop ℂ} {r : ℝ}
    (hfg : f =ᶠ[codiscreteWithin (sphere 0 |r|)] g) (hr : r ≠ 0) :
    proximity f a r = proximity g a r := by
  by_cases h : a = ⊤
  all_goals
    simp only [proximity, h, ↓reduceDIte]
    apply circleAverage_congr_codiscreteWithin _ hr
    filter_upwards [hfg] using by aesop

lemma proximity_congr_codiscrete {f g : ℂ → ℂ} {a : WithTop ℂ} {r : ℝ}
    (hfg : f =ᶠ[codiscrete ℂ] g) (hr : r ≠ 0) :
    proximity f a r = proximity g a r :=
  proximity_congr_codiscreteWithin (hfg.filter_mono (codiscreteWithin.mono (by tauto))) hr

lemma proximity_const {c : ℂ} {r : ℝ} :
    proximity (fun _ ↦ c) ⊤ r = posLog ‖c‖ := by
  simp [proximity, circleAverage_const]

end ValueDistribution


namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

lemma proximity_bounded_iff_constant {f : ℂ → ℂ} (h : AnalyticOnNhd ℂ f Set.univ) :
    (∃ c, f = fun _ ↦ c) ↔ proximity f ⊤ =O[atTop] (1 : ℝ → ℝ) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    simp_rw [isBigO_iff, eventually_atTop]
    use posLog ‖c‖
    simp [hc, proximity_const, abs_of_nonneg posLog_nonneg]
  · sorry

end ValueDistribution
