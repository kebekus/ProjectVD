import VD.PoissonJensen0

open Complex Filter Function MeromorphicOn Metric Real Set Classical Topology --ValueDistribution

/-!
## Additional Material
-/


/-!
## Formula goes here
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {x c w : ℂ} {f h : ℂ → ℂ}


open ComplexConjugate Metric Real

variable {R : ℝ} {w z : ℂ}

-- Proof by Aristotle

@[simp] theorem divisor_eq_zero_of_not_meromorphicOn {U : Set ℂ} {w : ℂ}
    (hf : ¬ MeromorphicOn f U) :
    divisor f U w = 0 := by
  unfold divisor
  aesop

@[simp] theorem divisor_eq_zero_of_meromorphicOrderAt_eq_zero {U : Set ℂ} {w : ℂ}
    (hf : meromorphicOrderAt f w = 0) :
    divisor f U w = 0 := by
  by_cases h₁f : MeromorphicOn f U
  · by_cases hw : w ∈ U
    <;> simp_all
  simp_all

@[simp] theorem divisor_nonneg_of_analyticOnNhd {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) :
    0 ≤ divisor f U := by
  intro x
  by_cases hx : x ∈ U
  <;> simp_all [hf.divisor_apply]

@[simp] theorem divisor_nonneg_apply {U : Set ℂ} {w : ℂ}
    (hf : 0 ≤ divisor f U) :
    0 ≤ divisor f U w := hf w

@[simp] lemma AnalyticAt.meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq_zero
    (h₁ : AnalyticAt ℂ f x) (h₂ : meromorphicOrderAt f x = 0) :
    meromorphicTrailingCoeffAt f x = f x := by
  apply h₁.meromorphicTrailingCoeffAt_of_ne_zero
  rw [h₁.meromorphicOrderAt_eq, ENat.map_natCast_eq_zero] at h₂
  have := analyticOrderAt_eq_zero.1 h₂
  simp_all


/--
The canonical factor has norm strictly greater than one for points inside the ball.
-/
theorem norm_canonicalFactor (h : w ∈ ball 0 R) (h₁z : z ∈ ball 0 R) (h₂z : z ≠ w) :
    1 < ‖canonicalFactor R w z‖ := by
  have h_norm : ‖R ^ 2 - conj w * z‖ > R * ‖z - w‖ := by
    simp_all [Complex.normSq, Complex.norm_def]
    rw [Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg _) h)] at *
    apply Real.lt_sqrt_of_sq_lt
    norm_cast
    rw [mul_pow, Real.sq_sqrt (by nlinarith)]
    nlinarith
  by_cases hR : R = 0
    <;> simp_all [canonicalFactor]
  rwa [one_lt_div (mul_pos (abs_pos.mpr hR) (norm_pos_iff.mpr (sub_ne_zero.mpr h₂z))),
    abs_of_pos (lt_of_le_of_lt (norm_nonneg _) h)]

theorem η₀
    (h₁w : w ∈ ball 0 R)
    (h₃w : meromorphicOrderAt f w = 0)
    (h₁f : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    Real.log ‖f w‖
      ≤ circleAverage (re ∘ herglotzRieszKernel 0 w * (log⁺ ‖f ·‖)) 0 R := by
  have h₄f : (divisor f (ball 0 R)).support.Finite := by
    apply ((divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
    intro b hb
    rw [mem_support, ne_eq, divisor_apply (fun x hx ↦ (h₁f x hx).meromorphicAt)
      (ball_subset_closedBall ((divisor f (ball 0 R)).supportWithinDomain hb))]
    rwa [mem_support, ne_eq, divisor_apply
      (fun c hc ↦ (fun x hx ↦ (h₁f x hx).meromorphicAt) c (ball_subset_closedBall hc))
      ((divisor f (ball 0 R)).supportWithinDomain hb)] at hb
  calc Real.log ‖f w‖
    _ = Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
      rw [AnalyticAt.meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq_zero
        (h₁f w (ball_subset_closedBall h₁w)) h₃w]
    _ ≤ circleAverage (re ∘ herglotzRieszKernel 0 w * (Real.log ‖f ·‖)) 0 R := by
      rw [poissonJensen₀ h₁w h₃w (fun x hx ↦ (h₁f x hx).meromorphicAt)]
      simp
      rw [finsum_eq_sum_of_support_subset (s := h₄f.toFinset) _ (fun _ _ ↦ by aesop)]
      apply Finset.sum_nonneg
      intro i hi
      apply mul_nonneg
      · simp_all [h₁f.mono ball_subset_closedBall]
      · have := (divisor f (ball 0 R)).supportWithinDomain
        apply log_nonneg (norm_canonicalFactor (by aesop) h₁w (by aesop)).le
    _ ≤ circleAverage (re ∘ herglotzRieszKernel 0 w * (log⁺ ‖f ·‖)) 0 R := by
      apply circleAverage_mono
      · sorry
      · sorry
      intro x hx
      simp
      unfold herglotzRieszKernel
      gcongr
      · trans (R - ‖w - 0‖) / (R + ‖w - 0‖)
        · simp only [sub_zero]
          simp only [mem_ball, dist_zero_right] at h₁w
          apply div_nonneg
          · apply sub_nonneg.2 h₁w.le
          · apply add_nonneg
            · apply (norm_nonneg w).trans h₁w.le
            · exact norm_nonneg w
        · apply le_re_herglotzRieszKernel
          · rwa [abs_of_pos (pos_of_mem_ball h₁w)] at hx
          · exact h₁w
      · -- should be simp
        unfold posLog
        simp
