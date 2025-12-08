import VD.MathlibPending.Nevanlinna_add_characteristic
import Mathlib.MeasureTheory.Integral.Prod

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution

namespace ValueDistribution

lemma analytic_measurable {f : ℂ → ℂ} (h : AnalyticOnNhd ℂ f ⊤) :
    Measurable f := by
  refine Continuous.borel_measurable ?_
  exact AnalyticOnNhd.continuous h

lemma meromorphic_measurable {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) :
    Measurable f := by
  apply?
  sorry

/-
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
-/

theorem cartan {r : ℝ} {f : ℂ → ℂ} (hr : r ≠ 0) (h : MeromorphicOn f ⊤) (h₂ : 0 < meromorphicOrderAt f 0) :
    characteristic f ⊤ r = circleAverage (logCounting f · r) 0 1 := by

  have f1 {a : ℂ} :
      logCounting f a r + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖
        = circleAverage (log ‖f · - a‖) 0 r + logCounting f ⊤ r := by
    have : logCounting f a r = logCounting (fun z ↦ f z - a) 0 r := by
      rw [logCounting_coe_eq_logCounting_sub_const_zero]
      rfl
    rw [this]
    have h₁ : MeromorphicOn (fun z ↦ f z - a) ⊤ := h.sub (MeromorphicOn.const a)
    have tmp := logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const h₁ hr
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
      circleAverage (fun a ↦ logCounting f a r + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 =
      circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 r + logCounting f ⊤ r) 0 1 := by
    apply circleAverage_congr_sphere
    intro a ha
    simp [f1]
  clear f1
  rw [circleAverage_fun_add (c := 0) (R := 1) (f₁ :=  fun a ↦ logCounting f a r)
    (f₂ := fun a ↦ log ‖meromorphicTrailingCoeffAt (fun x ↦ f x - a) 0‖)] at f2

  have σ₂ : circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (fun x ↦ f x - a) 0‖) 0 1 = 0 := by
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
  rw [σ₂] at f2
  clear σ₂
  simp at f2

  have σ₃ : circleAverage (fun a ↦ circleAverage (fun x ↦ log ‖f x - a‖) 0 r + logCounting f ⊤ r) 0 1
      = circleAverage (fun a ↦ circleAverage (fun x ↦ log ‖f x - a‖) 0 r) 0 1
        + circleAverage (fun a ↦ logCounting f ⊤ r) 0 1 := by
    apply circleAverage_fun_add
    · sorry
    · exact circleIntegrable_const (logCounting f ⊤ r) 0 1
  rw [σ₃] at f2
  clear σ₃

  have σ₄ : circleAverage (fun a ↦ logCounting f ⊤ r) 0 1 = logCounting f ⊤ r := by
    exact circleAverage_const (logCounting f ⊤ r) 0 1
  rw [σ₄] at f2
  clear σ₄

  rw [f2]
  clear f2

  unfold characteristic
  simp

  unfold proximity
  simp

  simp_rw [← circleAverage_log_norm_sub_const_eq_posLog]

  unfold circleAverage
  simp


  unfold intervalIntegral
  have : Ioc (2 * π) 0 = ∅ := by
    ext x
    simp
    intro hx
    trans 2 * π
    exact two_pi_pos
    exact hx
  simp [this]
  rw [MeasureTheory.integral_integral_swap]

  have {x y : ℝ} : ‖circleMap 0 1 y - f (circleMap 0 r x)‖ = ‖f (circleMap 0 r x) - circleMap 0 1 y‖ := by
    sorry
  simp_rw [this]

  have : Measurable f := by
    sorry

  · unfold uncurry
    simp
    refine (MeasureTheory.integrable_prod_iff ?_).mpr ?_
    · apply Measurable.aestronglyMeasurable (by fun_prop)
    · constructor
      · sorry
      · sorry
  · sorry
  · sorry


end ValueDistribution
