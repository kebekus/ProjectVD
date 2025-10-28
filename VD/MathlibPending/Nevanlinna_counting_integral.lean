import Mathlib.Analysis.Complex.JensenFormula

open Function MeromorphicOn Metric Real Set Classical ValueDistribution

namespace locallyFinsuppWithin

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*}

/--
Restriction commutes with taking positive parts.
-/
lemma restrict_posPart {V : Set X} (D : locallyFinsuppWithin U ℤ) (h : V ⊆ U) :
    D⁺.restrict h = (D.restrict h)⁺ := by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.posPart_apply]
  aesop

/--
Restriction commutes with taking negative parts.
-/
lemma restrict_negPart {V : Set X} (D : locallyFinsuppWithin U ℤ) (h : V ⊆ U) :
    D⁻.restrict h = (D.restrict h)⁻ := by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.negPart_apply]
  aesop

@[simp]
lemma toClosedBall_divisor {r : ℝ} {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) :
    (divisor f (closedBall 0 |r|)) = (locallyFinsuppWithin.toClosedBall r) (divisor f univ) := by
  simp_all [locallyFinsuppWithin.toClosedBall]

end locallyFinsuppWithin

/--
Relation between `ValueDistribution.logCounting` and
`locallyFinsuppWithin.logCounting`.
-/
lemma locallyFinsuppWithin.logCounting_divisor {f : ℂ → ℂ} :
    locallyFinsuppWithin.logCounting (divisor f ⊤) = logCounting f 0 - logCounting f ⊤ := by
  simp [logCounting, ← locallyFinsuppWithin.logCounting.map_sub]

/--
Over the complex numbers, present the logarithmic counting function attached to
the divisor of a meromorphic function `f` as a circle average over `log ‖f ·‖`.

This is a reformulation of Jensen's formula of Complex Analysis. See
`MeromorphicOn.circleAverage_log_norm` for Jensen's formula in the original
context.
-/
theorem locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const {R : ℝ} {f : ℂ → ℂ}
  (h : MeromorphicOn f ⊤) (hR : R ≠ 0) :
    locallyFinsuppWithin.logCounting (divisor f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have h₁f : MeromorphicOn f (closedBall 0 |R|) := by tauto
  simp only [MeromorphicOn.circleAverage_log_norm hR h₁f, locallyFinsuppWithin.logCounting, top_eq_univ, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    zero_sub, norm_neg, add_sub_cancel_right]
  congr 1
  · simp_all
  · rw [divisor_apply, divisor_apply]
    all_goals aesop

/--
Variant of
`locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const`, using
`ValueDistribution.logCounting` instead of `locallyFinsuppWithin.logCounting`.
-/
theorem ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const {R : ℝ} {f : ℂ → ℂ}
  (h : MeromorphicOn f ⊤) (hR : R ≠ 0) :
    (logCounting f 0 - logCounting f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  rw [← locallyFinsuppWithin.logCounting_divisor]
  exact locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const h hR
