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
  have tmp := logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const h₁ hR

  have : logCounting (fun z ↦ f z - a) ⊤ = logCounting f ⊤ := by
    have : (fun z ↦ f z - a) = f - fun z ↦ a := by rfl
    rw [this, logCounting_sub_const]
    exact h
  rw [this] at tmp
  clear this

  sorry

end ValueDistribution
