/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Integral.CircleAverage
import VD.meromorphicOn_integrability

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


/-!
# The Proximity Function of Value Distribution Theory
-/

open MeromorphicOn Metric Real Set

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : ℂ → ℂ} {a : WithTop ℂ} {a₀ : ℂ}

open Real

variable (f a) in
/--
The proximity function of a meromorphic function.

If `f : ℂ → ℂ` is meromorphic and `a : WithTop ℂ` is any value, this is a logarithmically weighted
measure of the number of times the function `f` takes a given value `a` within the disk `∣z∣ ≤ r`,
counting multiplicities.  In the special case where `a = ⊤`, it counts the poles of `f`.
-/
noncomputable def proximity : ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact fun R ↦ circleAverage (log⁺ ‖f ·‖) 0 R
  · exact fun R ↦ circleAverage (fun z ↦ log⁺ ‖1 / (f z - a.untop₀)‖) 0 R

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` is the counting
function associated with the zero-divisor of the meromorphic function `f - a₀`.
-/
lemma proximity_coe :
    proximity f a₀ = fun R ↦ circleAverage (fun z ↦ log⁺ ‖1 / (f z - a₀)‖) 0 R := by
  simp [proximity]

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` equals the logarithmic
counting function for the value zero of the shifted function `f - a₀`.
-/
lemma proximity_coe_eq_proximity_sub_const_zero :
    proximity f a₀ = proximity (f - fun _ ↦ a₀) 0 := by
  simp [proximity]

/--
The logarithmic counting function `logCounting f 0` is the counting function associated with the
zero-divisor of `f`.
-/
lemma proximity_zero :
    proximity f 0 = fun R ↦ circleAverage (log⁺ ‖f⁻¹ ·‖) 0 R := by
  simp [proximity]

/--
The logarithmic counting function `logCounting f ⊤` is the counting function associated with
the pole-divisor of `f`.
-/
lemma proximity_top :
    proximity f ⊤ = fun R ↦ circleAverage (log⁺ ‖f ·‖) 0 R := by
  simp [proximity]

/--
The counting function associated with the divisor of `f` is the difference between `logCounting f 0`
and `logCounting f ⊤`.
-/
theorem Nevanlinna_proximity {R : ℝ} (h₁f : MeromorphicOn f ⊤) :
  circleAverage (log ‖f ·‖) 0 R = proximity f ⊤ R - proximity f⁻¹ ⊤ R := by
  simp [proximity]
  rw [← circleAverage_sub]
  congr
  funext x
  simp_rw [← posLog_sub_posLog_inv];
  simp
  --
  apply MeromorphicOn.circleIntegrable_posLog_norm
  intro z hx
  exact h₁f z trivial
  --
  simp_rw [← norm_inv]
  apply MeromorphicOn.circleIntegrable_posLog_norm
  exact MeromorphicOn.inv_iff.mpr fun x a => h₁f x trivial

/-!
## Elementary Properties of the Counting Function
-/

/--
Relation between the logarithmic counting function of `f` and of `f⁻¹`.
-/
@[simp] theorem proximity_inv :
     proximity f⁻¹ ⊤ = proximity f 0 := by
  simp [proximity_zero, proximity_top]

end ValueDistribution
