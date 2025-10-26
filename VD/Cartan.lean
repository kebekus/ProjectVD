import VD.MathlibPending.Nevanlinna_counting_integral

open Function MeromorphicOn Metric Real Set Classical ValueDistribution

namespace ValueDistribution

theorem cartan {r : ℝ} {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) :
    characteristic f ⊤ r
      = circleAverage (logCounting f · r) 0 1 - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  sorry

end ValueDistribution
