import VD.MathlibSubmitted.Nevanlinna_counting_integral
import VD.MathlibSubmitted.Nevanlinna_add_proximity

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution


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

  have σ₁ (h₁ : meromorphicOrderAt f 0 < 0) :
      circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (fun x ↦ f x - a) 0‖) 0 1
        = log ‖meromorphicTrailingCoeffAt f 0‖ := by
    have {a : ℂ} : meromorphicTrailingCoeffAt (fun x ↦ f x - a) 0 = meromorphicTrailingCoeffAt f 0 := by
      have : (fun x ↦ f x - a) = f + fun _ ↦ -a := rfl
      rw [this]
      clear this
      apply MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt
      fun_prop
      rw [meromorphicOrderAt_const]
      simp_all
      by_cases ha: a = 0
      · simp [ha]
        exact lt_top_of_lt h₁
      simp [ha]
      exact h₁
    simp_rw [this]
    rw [circleAverage_const]

  have σ₂ (h₂ : 0 < meromorphicOrderAt f 0) :
      circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (fun x ↦ f x - a) 0‖) 0 1 = 0 := by
    have τ₁ {a : ℂ} (ha : a ≠ 0) : meromorphicTrailingCoeffAt (fun x ↦ f x - a) 0 = -a := by
      have : (fun x ↦ f x - a) = (fun _ ↦ -a) + f := by
        ext x
        simp
        ring
      rw [this]
      have : meromorphicTrailingCoeffAt (fun _ ↦ - a : ℂ → ℂ) 0 = -a := by
        exact meromorphicTrailingCoeffAt_const
      nth_rw 2 [← this]
      apply MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt
      · exact h 0 trivial
      · have : meromorphicOrderAt (fun _ ↦ -a : ℂ → ℂ) 0 = 0 := by
          refine (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff ?_).mpr ?_
          refine meromorphicNFAt_iff_analyticAt_or.mpr ?_
          left
          fun_prop
          simp_all
        rw [this]
        assumption
    rw [circleAverage_congr_sphere (f₂ := fun a ↦ log ‖-a‖)]
    simp_rw [norm_neg]
    have := circleAverage_log_norm_sub_const_eq_posLog (a := 0)
    simpa using this
    intro a ha
    simp
    rw [τ₁]
    simp
    aesop


  unfold characteristic
  unfold proximity
  simp

  all_goals sorry


end ValueDistribution
