import VD.MathlibPending.Cartan
import VD.ProximityAsymptotics

open Asymptotics Filter Function Metric Real Set Classical Topology ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E]

/-
Prove that the proximity function of an analytic function `f` is bounded if and
only if `f` is bounded and hence constant.
-/

@[simp] theorem posLog_nonneg' {x : ℝ} : 0 ≤ log⁺ x := by simp [posLog]

namespace ValueDistribution

theorem proximity_bounded_iff_constant {f : ℂ → ℂ} (h : AnalyticOnNhd ℂ f Set.univ) :
    (∃ c, f = fun _ ↦ c) ↔ proximity f ⊤ =O[atTop] (1 : ℝ → ℝ) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    simp_rw [isBigO_iff, eventually_atTop]
    use posLog ‖c‖
    simp [hc, proximity_const, abs_of_nonneg posLog_nonneg]
  · intro h₁
    rw [logCounting_isBigO_one_iff_analyticOnNhd h] at h₁
    tauto

theorem proximity_bounded_if_eventuallyConstant {f : ℂ → E} (h : EventuallyConst f (codiscrete ℂ)) :
    proximity f ⊤ =O[atTop] (1 : ℝ → ℝ) := by
  rw [eventuallyConst_iff_exists_eventuallyEq] at h
  obtain ⟨c, hc⟩ := h
  simp_rw [isBigO_iff, eventually_atTop]
  use log⁺ ‖c‖, 1, fun _ _ ↦ by simp [proximity_congr_codiscrete hc (by linarith), abs_of_nonneg]

end ValueDistribution
