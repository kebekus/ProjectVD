import VD.MathlibSubmitted.ComplexMeanvalue

open Asymptotics Complex ComplexConjugate Filter Function Metric Real Set Classical Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}


theorem circleAverage_of_differentiable_on₂ (hf : ∀ z ∈ closedBall c |R|, DifferentiableAt ℂ f z)
    (hw : w ∈ ball c |R|) (h₁w : w ≠ c) (hR : 0 < R) :
    circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R = f w := by

  let W := R * R / (conj (w - c))
  have : R < ‖W‖ := by
    unfold W
    rw [norm_div, norm_conj]
    rw [mem_ball, dist_eq_norm, abs_of_pos hR] at hw
    norm_num
    rw [← mul_div, lt_mul_iff_one_lt_right hR, one_lt_div_iff]
    left
    constructor
    · simp [h₁w, sub_eq_zero]
    · exact hw

  have τ₂ : ∀ z ∈ closedBall c |R|, DifferentiableAt ℂ (fun x ↦ (x - (W + c))⁻¹ • f x) z := by
    intro z hz
    apply DifferentiableAt.fun_smul _ (hf z hz)
    · apply DifferentiableAt.fun_inv _ _
      · fun_prop
      · by_contra h
        rw [sub_eq_zero] at h
        subst h
        simp at hz
        grind

  have τ₁ : DiffContOnCl ℂ (fun x ↦ (x - c)⁻¹ • (x - (W + c))⁻¹ • f x) (ball c R) := by
    sorry

  have τ₀ : circleAverage (fun x ↦ (x - (W + c))⁻¹ • f x) c R = 0 := by
    rw [circleAverage_eq_circleIntegral (ne_of_lt hR).symm]
    rw [τ₁.circleIntegral_eq_zero hR.le]
    simp

  rw [← zero_add (a := circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R)]
  rw [← τ₀]
  rw [← circleAverage_fun_add]
  simp_rw [← add_smul]



  /-
  circleAverage_of_differentiable_on_off_countable₁ countable_empty
    (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt)
    (fun z hz ↦ hf z (by simp_all [le_of_lt])) hw hR
  -/
  sorry
