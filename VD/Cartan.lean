import VD.MathlibPending.Nevanlinna_counting_integral
import VD.MathlibPending.Nevanlinna_add_proximity

open Function MeromorphicOn Metric Real Set Classical ValueDistribution

namespace ValueDistribution

theorem cartan {r : ℝ} {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) :
    characteristic f ⊤ r
      = circleAverage (logCounting f · r) 0 1 - log ‖meromorphicTrailingCoeffAt f 0‖ := by

  have R : ℝ := by sorry
  have hR : R ≠ 0 := by sorry

  have f1 {a : ℂ} :
      logCounting f a R + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖
        = circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R := by
    have : logCounting f a R = logCounting (fun z ↦ f z - a) 0 R := by
      rw [logCounting_coe_eq_logCounting_sub_const_zero]
      rfl
    rw [this]
    have h₁ : MeromorphicOn (fun z ↦ f z - a) ⊤ :=
      h.sub (MeromorphicOn.const a)
    have tmp := logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const h₁ hR
    have : logCounting (f · - a) ⊤ = logCounting f ⊤ := by
      have : (f · - a) = f - fun _ ↦ a := by rfl
      rw [this, logCounting_sub_const]
      exact h
    rw [this] at tmp
    clear this
    simp at tmp
    rw [sub_eq_iff_eq_add] at tmp
    rw [tmp]
    abel

  have f2 :
      circleAverage (fun a ↦ logCounting f a R + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 =
      circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R) 0 1 := by
    apply circleAverage_congr_sphere
    intro a ha
    simp [f1]
  clear f1

  rw [circleAverage_add_fun (c := 0) (R := 1) (f₁ :=  fun a ↦ logCounting f a R)
    (f₂ := fun a ↦ log ‖meromorphicTrailingCoeffAt (fun x ↦ f x - a) 0‖)] at f2

  sorry


end ValueDistribution
