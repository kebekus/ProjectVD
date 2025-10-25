import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import VD.MathlibSubmitted.DivisorOrder

open Function MeromorphicOn Metric Real Set Classical ValueDistribution

namespace locallyFinsuppWithin

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*}

lemma restrictPosPart {V : Set X} (D : locallyFinsuppWithin U ℤ) (h : V ⊆ U) :
    D⁺.restrict h = (D.restrict h)⁺ := by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.posPart_apply]
  aesop

lemma restrictNegPart {V : Set X} (D : locallyFinsuppWithin U ℤ) (h : V ⊆ U) :
    D⁻.restrict h = (D.restrict h)⁻ := by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.negPart_apply]
  aesop

end locallyFinsuppWithin

lemma lcd {f : ℂ → ℂ} :
    locallyFinsuppWithin.logCounting (divisor f ⊤) = logCounting f 0 - logCounting f ⊤ := by
  simp [logCounting, ← locallyFinsuppWithin.logCounting.map_sub]


/--
Reformulation of Jensen's formula: Up to a constant, the logarithmic counting
function attached to the divisor of a meromorphic function `f` equals the circle
average of `log ‖f‖`.

See `MeromorphicOn.circleAverage_log_norm` for Jensen's formula in the original
context.
-/
theorem locallyFinsuppWithin.logCounting_eq_circleAverage_sub_const {R : ℝ} {f : ℂ → ℂ}
  (h : MeromorphicOn f ⊤) (hR : R ≠ 0) :
    locallyFinsuppWithin.logCounting (divisor f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have h₁f : MeromorphicOn f (closedBall 0 |R|) := by tauto
  simp only [MeromorphicOn.circleAverage_log_norm hR h₁f, locallyFinsuppWithin.logCounting, top_eq_univ, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    zero_sub, norm_neg, add_sub_cancel_right]
  congr 1
  · have {r : ℝ} : (locallyFinsuppWithin.toClosedBall r) (divisor f univ)
        = (divisor f (closedBall 0 |r|)) := by
      unfold locallyFinsuppWithin.toClosedBall
      aesop
    simp_rw [this]
  · aesop
