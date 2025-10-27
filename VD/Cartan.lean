import VD.MathlibPending.Nevanlinna_counting_integral

open Function MeromorphicOn Metric Real Set Classical ValueDistribution

namespace ValueDistribution

theorem cartan {r : ℝ} {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) :
    characteristic f ⊤ r
      = circleAverage (logCounting f · r) 0 1 - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have a : ℂ := by sorry
  have h₁ : MeromorphicOn (fun z ↦ f z - a) ⊤ :=
    h.sub (MeromorphicOn.const a)

  have R : ℝ := by sorry
  have hR : R ≠ 0 := by sorry
  have := logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const h₁ hR

  sorry

end ValueDistribution
