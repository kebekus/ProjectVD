import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import VD.Jensen

open Function.locallyFinsuppWithin MeromorphicAt MeromorphicOn Metric Real

variable
  {f : ℂ → ℂ} {R : ℝ}

namespace ValueDistribution

/-!
## First Part of the First Main Theorem
-/

/--
Helper lemma for the first part of the First Main Theorem: Given a meromorphic
function `f`, compute difference between the characteristic functions of `f` and
of its inverse.
-/
lemma characteristic_sub_characteristic_inv (h : MeromorphicOn f ⊤) :
    characteristic f ⊤ - characteristic f⁻¹ ⊤ =
      circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ).logCounting := by
  calc characteristic f ⊤ - characteristic f⁻¹ ⊤
  _ = proximity f ⊤ - proximity f⁻¹ ⊤ - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    unfold characteristic
    ring
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    rw [proximity_sub_proximity_inv_eq_circleAverage h]
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f 0 - logCounting f ⊤) := by
    rw [logCounting_inv]
  _ = circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ).logCounting := by
    rw [← ValueDistribution.log_counting_zero_sub_logCounting_top]

/--
First part of the First Main Theorem: Away from zero, the difference between the
characteristic functions of `f` and `f⁻¹` equals `log ‖leadCoefficient f 0‖`.
-/
@[simp]
theorem characteristic_sub_characteristic_inv_at_zero (hf : MeromorphicOn f ⊤) (hR : R ≠ 0) :
    characteristic f ⊤ R - characteristic f⁻¹ ⊤ R = log ‖meromorphicTrailingCoeffAt f 0‖ := by
  calc characteristic f ⊤ R - characteristic f⁻¹ ⊤ R
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) R  := by simp
  _ = circleAverage (log ‖f ·‖) 0 R - (divisor f Set.univ).logCounting R := by
    rw [characteristic_sub_characteristic_inv hf]
    rfl
  _ = log ‖meromorphicTrailingCoeffAt f 0‖ := by
    rw [JensenFormula hR (hf.mono_set (by tauto))]
    unfold Function.locallyFinsuppWithin.logCounting
    have : (divisor f (closedBall 0 |R|)) = (divisor f Set.univ).toClosedBall R :=
      (divisor_restrict hf (by tauto)).symm
    simp [this, toClosedBall, restrictMonoidHom, restrict_apply]

/--
Complement to the first part of the First Main Theorem: At 0, the difference
between the characteristic functions of `f`  and `f⁻¹` equals `log ‖f 0‖`.
-/
@[simp]
theorem characteristic_sub_characteristic_inv_off_zero (h : MeromorphicOn f ⊤) :
    characteristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0 = log ‖f 0‖ := by
  calc characteristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) 0 := by simp
  _ = circleAverage (log ‖f ·‖) 0 0 - (divisor f Set.univ).logCounting 0 := by
    rw [ValueDistribution.characteristic_sub_characteristic_inv h]
    rfl
  _ = log ‖f 0‖ := by
    simp

end ValueDistribution
