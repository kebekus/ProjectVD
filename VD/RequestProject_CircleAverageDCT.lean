import Mathlib

open Filter Metric Real MeasureTheory Set Topology

/-!
## Herglotz–Riesz kernel
-/

/-- The integrand in our application: `Re((z + w)/(z - w)) · log ‖z - ρ‖`. -/
noncomputable def herglotzLogIntegrand (w ρ : ℂ) : ℂ → ℝ :=
  (Complex.re ∘ herglotzRieszKernel 0 w) • (fun z ↦ log ‖z - ρ‖)


-- Continuity of the herglotzLogIntegrand
private lemma herglotzLogIntegrand_continuousAt {w ρ z : ℂ} (hz_w : z ≠ w) (hz_ρ : z ≠ ρ) :
    ContinuousAt (herglotzLogIntegrand w ρ) z := by
  have : ‖z - ρ‖ ≠ 0 := by simp_all [sub_eq_zero]
  simp only [herglotzLogIntegrand, herglotzRieszKernel_fun_def, sub_zero, smul_eq_mul]
  fun_prop (disch := grind)

-- Continuity of the herglotzLogIntegrand
private lemma herglotzLogIntegrand_continuous_on_circle
    {w ρ : ℂ} {R r : ℝ} (hR : 0 < R) (hρ : ‖ρ‖ = R)
    (hr_pos : 0 < r) (hr_lt : r < R) (hwr : ‖w‖ < r) :
    Continuous (fun θ => herglotzLogIntegrand w ρ (circleMap 0 r θ)) := by
  rw [continuous_iff_continuousAt]
  intro θ
  apply ContinuousAt.comp _ (by fun_prop)
  apply herglotzLogIntegrand_continuousAt
  · by_contra h
    rw [← h, norm_circleMap_zero] at hwr
    grind
  · by_contra h
    rw [← h, norm_circleMap_zero] at hρ
    grind

lemma norm_sq_circleMap_sub_lower_bound
    {r₀ r R : ℝ} {ρ : ℂ} (hρ : ‖ρ‖ = R)
    (hr₀ : 0 < r₀) (hR : 0 < R) (hr₀r : r₀ ≤ r) (hrR : r ≤ R) (θ : ℝ) :
    (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ^ 2 ≤ ‖circleMap 0 r θ - ρ‖ ^ 2 := by
  -- By the cosine law, we have ‖circleMap 0 r θ - ρ‖² = r² + R² - 2rR cos(θ - α) and ‖circleMap 0 R θ - ρ‖² = R² + R² - 2R² cos(θ - α).
  have h_cos_law : ‖circleMap 0 r θ - ρ‖ ^ 2 = r ^ 2 + R ^ 2 - 2 * r * R * cos (θ - Complex.arg ρ)
      ∧ ‖circleMap 0 R θ - ρ‖ ^ 2 = R ^ 2 + R ^ 2 - 2 * R ^ 2 * cos (θ - Complex.arg ρ) := by
    norm_num [ Complex.normSq, Complex.sq_norm, circleMap ];
    rw [← Complex.norm_mul_cos_arg ρ, ← Complex.norm_mul_sin_arg ρ]
    ring_nf
    norm_num [sin_sub, cos_sub, hρ]
    constructor
    <;> rw [sin_sq, sin_sq]
    <;> ring;
  rw [div_mul_eq_mul_div, div_le_iff₀]
  <;> nlinarith [mul_le_mul_of_nonneg_left hr₀r hR.le, mul_le_mul_of_nonneg_left hrR hR.le,
    neg_one_le_cos, cos_le_one]

lemma norm_circleMap_sub_lower_bound
    {r₀ r R : ℝ} {ρ : ℂ} (hρ : ‖ρ‖ = R)
    (hr₀ : 0 < r₀) (hR : 0 < R) (hr₀r : r₀ ≤ r) (hrR : r ≤ R) (θ : ℝ) :
    sqrt (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ≤ ‖circleMap 0 r θ - ρ‖ := by
  convert sqrt_le_sqrt (norm_sq_circleMap_sub_lower_bound hρ hr₀ hR hr₀r hrR θ) using 1
  norm_num [hr₀.le, hR.le]
  aesop

lemma herglotzLogIntegrand_bound
  {w ρ : ℂ} {R r₀ r : ℝ} (hR : 0 < R) (hρ : ‖ρ‖ = R)
  (hr₀ : 0 < r₀) (hw : ‖w‖ < r₀) (hr₀r : r₀ ≤ r) (hrR : r ≤ R) (θ : ℝ)
  (hdR : 0 < ‖circleMap 0 R θ - ρ‖) :
  ‖herglotzLogIntegrand w ρ (circleMap 0 r θ)‖ ≤
    ((R + ‖w‖) / (r₀ - ‖w‖)) * (|log (2 * R)| + |log (sqrt (r₀ / R))| + |log ‖circleMap 0 R θ - ρ‖|) := by
  simp only [herglotzLogIntegrand, Pi.smul_apply', Function.comp_apply, smul_eq_mul, norm_mul, norm_eq_abs]
  gcongr
  · apply div_nonneg (by linarith [norm_nonneg w]) (by linarith [norm_nonneg w])
  · trans (r + ‖w‖) / (r - ‖w‖)
    · simp only [herglotzRieszKernel, sub_zero]
      apply le_trans (Complex.abs_re_le_norm _)
      rw [norm_div]
      gcongr
      · apply add_nonneg (by grind) (norm_nonneg w)
      · grind
      · apply le_trans (norm_add_le _ _)
        grind [norm_circleMap_zero, add_le_add_iff_right]
      · convert norm_sub_norm_le (circleMap 0 r θ) w
        grind [norm_circleMap_zero]
    · gcongr
      linarith
  · refine' abs_le.mpr ⟨ _, _ ⟩
    · have h_log_lower_bound : log ‖circleMap 0 r θ - ρ‖ ≥ log (sqrt (r₀ / R)) + log ‖circleMap 0 R θ - ρ‖ := by
        rw [← log_mul (by positivity) (by positivity)]
        exact log_le_log
          (mul_pos (sqrt_pos.mpr (div_pos hr₀ hR)) hdR)
          (by linarith [norm_circleMap_sub_lower_bound hρ hr₀ hR hr₀r hrR θ])
      grind
    · refine' le_trans _ (le_add_of_le_of_nonneg (le_add_of_nonneg_right <| abs_nonneg _ ) <| abs_nonneg _)
      refine' le_trans (log_le_log _ _) (le_abs_self _)
      · refine' lt_of_lt_of_le _ (norm_circleMap_sub_lower_bound hρ hr₀ hR hr₀r hrR θ)
        aesop
      · apply le_trans (norm_sub_le _ _)
        simp only [circleMap, zero_add, Complex.norm_mul, Complex.norm_real, norm_eq_abs,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        linarith [abs_of_nonneg (by linarith : 0 ≤ r)]

/-!
## The specific convergence result
-/

private theorem herglotzLogIntegrand_circleAverage_tendsto
    {ρ w : ℂ} {R : ℝ} (hR : 0 < R) (hρ : ‖ρ‖ = R) (hw : ‖w‖ < R)
    {r : ℕ → ℝ} (hr_lt : ∀ n, r n < R) (hr_pos : ∀ n, 0 < r n)
    (hr_tendsto : Tendsto r atTop (nhds R)) :
    Tendsto (fun n ↦ circleAverage (herglotzLogIntegrand w ρ) 0 (r n)) atTop
      (nhds (circleAverage (herglotzLogIntegrand w ρ) 0 R)) := by
  -- Apply the dominated convergence theorem.
  let bound := fun θ ↦ ((R + ‖w‖) / ((R + ‖w‖) / 2 - ‖w‖)) * (|log (2 * R)| + |log (sqrt ((R + ‖w‖) / 2 / R))| + |log ‖circleMap 0 R θ - ρ‖|)
  apply Filter.Tendsto.smul tendsto_const_nhds _
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
  · -- The herglotzLogIntegrand is AEStronglyMeasurable
    filter_upwards [hr_tendsto.eventually (lt_mem_nhds hw) ] with n hn
    apply Continuous.aestronglyMeasurable
    apply_rules [herglotzLogIntegrand_continuous_on_circle]
  · -- Pointwise boundedness outside a null set
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, r n > (R + ‖w‖) / 2 :=
      Filter.eventually_atTop.mp (hr_tendsto.eventually (lt_mem_nhds (by linarith)))
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have h_bound {θ : ℝ} : ‖herglotzLogIntegrand w ρ (circleMap 0 (r n) θ)‖ ≤ bound θ ∨ ‖circleMap 0 R θ - ρ‖ = 0 := by
      by_cases h : ‖circleMap 0 R θ - ρ‖ = 0
      <;> simp_all [bound, circleMap]
      convert herglotzLogIntegrand_bound hR hρ
        (show 0 < (R + ‖w‖) / 2 by linarith [norm_nonneg w])
        (show ‖w‖ < (R + ‖w‖) / 2 by linarith [norm_nonneg w])
        (show (R + ‖w‖) / 2 ≤ r n by linarith [hN n hn])
        (show r n ≤ R by linarith [hr_lt n]) θ _
        using 1
      · norm_num [circleMap]
      · norm_num [circleMap]
      · exact norm_pos_iff.mpr (by simpa [circleMap] using h)
    apply MeasureTheory.measure_mono_null (t := {θ | ‖circleMap 0 R θ - ρ‖ = 0}) (by grind)
    apply Set.Countable.measure_zero _ MeasureTheory.MeasureSpace.volume
    simp only [norm_eq_zero, sub_eq_zero]
    exact (countable_singleton ρ).preimage_circleMap 0 (hR.ne')
  · -- IntervalIntegrable bound volume 0 (2 * π)
    apply IntervalIntegrable.const_mul
    apply IntervalIntegrable.add
    · exact IntervalIntegrable.add (by simp) (by continuity)
    · apply IntervalIntegrable.abs
      exact circleIntegrable_log_norm_meromorphicOn (f := fun z ↦ z - ρ)
        (fun x hx ↦ by fun_prop)
  · -- Pointwise convergence outside a null set
    have h_measure_zero : MeasureTheory.volume {θ : ℝ | circleMap 0 R θ = w ∨ circleMap 0 R θ = ρ} = 0 := by
      apply Set.Countable.measure_zero _ MeasureTheory.MeasureSpace.volume
      exact Set.Countable.union ((countable_singleton w).preimage_circleMap 0 (hR.ne'))
          ((countable_singleton ρ).preimage_circleMap 0 (hR.ne'))
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_measure_zero] with θ hθ
    intro _
    apply (herglotzLogIntegrand_continuousAt (by tauto) (by tauto)).tendsto.comp
    apply Filter.Tendsto.add tendsto_const_nhds
      (Filter.Tendsto.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hr_tendsto)
        tendsto_const_nhds)

theorem xx (w ρ : ℂ)
    {R : ℝ} (hR : 0 < R) (hρ : ‖ρ‖ = R) (hw : ‖w‖ < R)  :
    circleAverage (herglotzLogIntegrand w ρ) (0 : ℂ) R = log ‖w - ρ‖ := by
  let r : ℕ → ℝ := fun n ↦ R - (R - ‖w‖) / (n + 2)
  have hr_lt : ∀ n, r n < R := by
    intro n
    simp_all only [sub_lt_self_iff, sub_pos, div_pos_iff_of_pos_left, r]
    linarith
  have hr_pos : ∀ n, 0 < r n := by
    intro n
    simp_all only [sub_lt_self_iff, sub_pos, div_pos_iff_of_pos_left, r]
    apply (div_lt_iff₀ (by linarith)).2
    calc R - ‖w‖
      _ ≤ R := by aesop
      _ < R * (n + 2) := by
        rw [lt_mul_iff_one_lt_right hR]
        linarith
  have hr_tendsto : Tendsto r atTop (nhds R) :=
    le_trans (tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <|
      Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      (by norm_num)
  have DCT := herglotzLogIntegrand_circleAverage_tendsto hR hρ hw hr_lt hr_pos hr_tendsto
  have {n : ℕ} : circleAverage (herglotzLogIntegrand w ρ) 0 (r n) = log ‖w - ρ‖ := by
    unfold herglotzLogIntegrand
    rw [InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul]
    · constructor
      · intro z hz
        have : z ≠ ρ := by
          by_contra h
          simp only [mem_ball, dist_zero_right] at hz
          grind
        apply AnalyticAt.harmonicAt_log_norm (by fun_prop) (by grind)
      · intro x hx
        apply ContinuousAt.continuousWithinAt
        have : ‖x - ρ‖ ≠ 0 := by
          by_contra h
          rw [norm_eq_zero, sub_eq_zero] at h
          rw [closure_ball _ (by grind), mem_closedBall, dist_zero_right] at hx
          grind
        fun_prop (disch := grind)
    · simp [r, lt_sub_iff_add_lt]
      apply add_lt_of_lt_neg_add
      nth_rw 2 [add_comm]
      rw [← sub_eq_add_neg]
      exact div_lt_self (by simp_all) (by linarith)
  aesop
