import VD.PoissonJensen0
import VD.MathlibSubmitted.Translation

open Complex Filter Function MeromorphicOn Metric Real Set Classical Topology --ValueDistribution



/-!
## Formula goes here
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {x c w : ℂ} {f h : ℂ → ℂ}


theorem poissonJensen {c : ℂ}
    (h₁w : w ∈ ball c R)
    (h₃w : meromorphicOrderAt f w = 0)
    (h₁f : MeromorphicOn f (closedBall c R)) :
    Real.log ‖meromorphicTrailingCoeffAt f w‖
      = circleAverage (re ∘ herglotzRieszKernel c w * (Real.log ‖f ·‖)) c R
        - ∑ᶠ i, (divisor f (ball c R) i) * Real.log ‖canonicalFactor R (i - c) (w - c)‖ := by
  let g := fun z ↦ f (z + c)
  have : f = fun z ↦ g (z - c) := by simp [g]
  repeat rw [this]
  simp
  have : meromorphicTrailingCoeffAt (fun z ↦ g (z - c)) w = meromorphicTrailingCoeffAt g (w - c) := by
    rw [← this]
    exact (meromorphicTrailingCoeffAt_fun_comp_add_const_eq_meromorphicTrailingCoeffAt
      (f := f) (c := c) (x := w)).symm
  rw [this]
  rw [poissonJensen₀ (R := R)]
  congr 1
  · simp only [← Real.circleAverage_map_add_const (c := c), Pi.mul_apply, comp_apply,
      add_sub_cancel_right]
    congr
    ext x
    exact (herglotzRieszKernel_add_const c w x).symm
  · -- Translate the finsum by `i ↦ i + c`: a zero of `f` at `i + c` corresponds to a
    -- zero of `g` at `i`, and the canonical factors match accordingly.
    apply finsum_eq_of_bijective (fun i ↦ i + c) (Equiv.addRight c).bijective
    intro x
    simp only [add_sub_cancel_right, divisor_ball_fun_comp_add_const_eq_divisor_ball]
  · rw [mem_ball_iff_norm] at h₁w
    simpa [mem_ball_zero_iff] using h₁w
  · show meromorphicOrderAt (fun z ↦ f (z + c)) (w - c) = 0
    rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
    exact h₃w
  · have hf : (fun z ↦ g (z - c)) = f := funext fun z ↦ by simp [g]
    rw [← meromorphicOn_closedBall_fun_comp_sub_const_iff_meromorphicOn_closedBall (c := c), hf]
    exact h₁f
