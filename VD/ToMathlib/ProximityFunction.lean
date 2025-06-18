/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.Complex.ValueDistribution.ProximityFunction

/-!
# Circle Averages
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
  {f f₁ f₂ : ℂ → E} {c : ℂ} {R : ℝ} {a : 𝕜}

open Real

/-- Circle averages commute with subtraction. -/
theorem circleAverage_sub (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (f₁ - f₂) c R = circleAverage f₁ c R - circleAverage f₂ c R := by
  rw [circleAverage, circleAverage, circleAverage, ← smul_sub]
  congr
  apply intervalIntegral.integral_sub hf₁ hf₂

open MeromorphicOn Metric Real Set

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E]
  {f g : ℂ → E} {a : WithTop E} {a₀ : E}

open Real

/--
For complex-valued `f`, the difference between `proximity f ⊤` and `proximity
f⁻¹ ⊤` is the circle average of `log ‖f ·‖`.
-/
theorem proximity_sub_proximity_inv_eq_circleAverage {f : ℂ → ℂ} (h₁f : MeromorphicOn f ⊤) :
    proximity f ⊤ - proximity f⁻¹ ⊤ = circleAverage (log ‖f ·‖) 0 := by
  ext R
  have : CircleIntegrable (log⁺ ‖f ·‖⁻¹) 0 R := by
    simp_rw [← norm_inv]
    apply circleIntegrable_posLog_norm_meromorphicOn (h₁f.inv.mono_set (by tauto))
  simp only [proximity, ↓reduceDIte, Pi.inv_apply, norm_inv, Pi.sub_apply]
  rw [← circleAverage_sub]
  simp_rw [← posLog_sub_posLog_inv]
  rfl
  · apply circleIntegrable_posLog_norm_meromorphicOn (h₁f.mono_set (by tauto))
  · simp_rw [← norm_inv]
    apply circleIntegrable_posLog_norm_meromorphicOn  (h₁f.inv.mono_set (by tauto))

end ValueDistribution
