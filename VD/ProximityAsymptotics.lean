import VD.PoissonJensen0
import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic

open Complex Filter Function MeromorphicOn Metric Real Set Classical Topology --ValueDistribution

/-!
## Additional Material
-/


/-!
## Formula goes here
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {R : ℝ} {x c w : ℂ} {f h : ℂ → ℂ}


open ComplexConjugate Metric Real

variable {R : ℝ} {w z : ℂ}


-- Proof by Aristotle

@[fun_prop] theorem continuous_posLog : Continuous log⁺ := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · apply ContinuousAt.congr (f := fun _ ↦ 0) (by fun_prop)
    filter_upwards [Metric.ball_mem_nhds _ zero_lt_one ] with y hy
    rw [eq_comm, posLog_eq_zero_iff y]
    simp_all [le_of_lt]
  unfold posLog
  fun_prop

@[fun_prop]
theorem Real.Continuous.circleAverage {f : ℂ → E}
    (hf : Continuous f) :
    Continuous (Real.circleAverage f c) := by
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  fun_prop

@[fun_prop]
theorem continuous_proximity (h₁f : Continuous f) :
    Continuous (ValueDistribution.proximity f ⊤) := by
  unfold ValueDistribution.proximity
  simp only [reduceDIte]
  fun_prop

theorem analyticOnNhd_herglotzRieszKernel_compl :
    AnalyticOnNhd ℂ (herglotzRieszKernel c w) {w}ᶜ := by
  intro x hx
  unfold herglotzRieszKernel
  have : x - w ≠ 0 := by grind
  fun_prop (disch := aesop)

@[fun_prop]
theorem continuousOn_herglotzRieszKernel_sphere (hw : w ∈ ball c R):
    ContinuousOn (re ∘ herglotzRieszKernel c w) (sphere c |R|) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.comp (by fun_prop) (analyticOnNhd_herglotzRieszKernel_compl x _).continuousAt
  by_contra h
  simp only [mem_compl_iff, mem_singleton_iff, not_not] at h
  rw [← h, ← abs_of_pos (pos_of_mem_ball hw), mem_ball_iff_norm] at hw
  simp_all

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable,
then `g • f` is circle integrable.
-/
theorem CircleIntegrable.continuousOn_smul
    {E 𝕜 : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    {f : ℂ → E} {g : ℂ → 𝕜} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (g • f) c R :=
  IntervalIntegrable.continuousOn_smul hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable,
then `g • f` is circle integrable.
-/
theorem CircleIntegrable.continuousOn_fun_smul
    {E 𝕜 : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    {f : ℂ → E} {g : ℂ → 𝕜} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (fun z ↦ g z • f z) c R :=
  hf.continuousOn_smul hg

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable,
then `g * f` is circle integrable.
-/
theorem CircleIntegrable.continuousOn_mul
    {𝕜 : Type*} [NormedRing 𝕜]
    {f g : ℂ → 𝕜} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (g * f) c R :=
  IntervalIntegrable.continuousOn_mul hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable,
then `g * f` is circle integrable.
-/
theorem CircleIntegrable.continuousOn_fun_mul
    {𝕜 : Type*} [NormedRing 𝕜]
    {f g : ℂ → 𝕜} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (fun z ↦ g z * f z) c R :=
  hf.continuousOn_mul hg

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
      ≤ ((R + ‖w‖) / (R - ‖w‖)) * circleAverage (log⁺ ‖f ·‖) 0 R := by
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
      · apply CircleIntegrable.continuousOn_mul _ (continuousOn_herglotzRieszKernel_sphere h₁w)
        apply circleIntegrable_log_norm
        intro x hx
        rw [abs_of_pos (pos_of_mem_ball h₁w)] at hx
        apply (h₁f x (sphere_subset_closedBall hx)).meromorphicAt
      · apply CircleIntegrable.continuousOn_mul _ (continuousOn_herglotzRieszKernel_sphere h₁w)
        apply circleIntegrable_posLog_norm
        intro x hx
        rw [abs_of_pos (pos_of_mem_ball h₁w)] at hx
        apply (h₁f x (sphere_subset_closedBall hx)).meromorphicAt
      intro x hx
      simp
      unfold herglotzRieszKernel
      gcongr
      · trans (R - ‖w - 0‖) / (R + ‖w - 0‖)
        · rw [sub_zero]
          simp only [mem_ball, dist_zero_right] at h₁w
          apply div_nonneg (sub_nonneg.2 h₁w.le)
            (add_nonneg ((norm_nonneg w).trans h₁w.le) (norm_nonneg w))
        · apply le_re_herglotzRieszKernel _ h₁w
          rwa [abs_of_pos (pos_of_mem_ball h₁w)] at hx
      · -- should be simp
        unfold posLog
        simp
    _ ≤ circleAverage ( ((R + ‖w‖) / (R - ‖w‖)) • (log⁺ ‖f ·‖)) 0 R := by
      apply circleAverage_mono
      · apply CircleIntegrable.continuousOn_mul _ (continuousOn_herglotzRieszKernel_sphere h₁w)
        apply circleIntegrable_posLog_norm
        intro x hx
        rw [abs_of_pos (pos_of_mem_ball h₁w)] at hx
        apply (h₁f x (sphere_subset_closedBall hx)).meromorphicAt
      · apply CircleIntegrable.continuousOn_mul
        · apply circleIntegrable_posLog_norm
          intro x hx
          rw [abs_of_pos (pos_of_mem_ball h₁w)] at hx
          apply (h₁f x (sphere_subset_closedBall hx)).meromorphicAt
        · fun_prop
      intro x hx
      rw [abs_of_pos (pos_of_mem_ball h₁w)] at hx
      simp
      gcongr
      · exact posLog_nonneg
      · simpa [herglotzRieszKernel] using re_herglotzRieszKernel_le hx h₁w
    _ = ((R + ‖w‖) / (R - ‖w‖)) * circleAverage (log⁺ ‖f ·‖) 0 R := by
      apply circleAverage_smul

theorem η₁
    (h₁f : AnalyticOnNhd ℂ f univ) :
    Real.log ‖f w‖ ≤ 3 * ValueDistribution.proximity f ⊤ ‖2 * w‖ := by
  by_cases h₁w : f w = 0
  · simp_all
    apply ValueDistribution.proximity_nonneg
  rw [ValueDistribution.proximity_top]
  by_cases h₂w : w = 0
  · simp_all
    rw [← one_mul (a := Real.log ‖f 0‖), mul_comm, mul_comm (a := 3)]
    gcongr
    · exact posLog_nonneg
    · simp [posLog]
    · norm_num
  have h₁w : w ∈ ball 0 (2 * ‖w‖) := by aesop
  by_cases h₃w : meromorphicOrderAt f w ≠ 0
  · have : f w = 0 := by
      have := h₁f w (by tauto)
      rw [← this.analyticOrderAt_ne_zero]
      rw [this.meromorphicOrderAt_eq] at h₃w
      aesop
    simp_all
  rw [ne_eq, not_not] at h₃w
  have h₁f : AnalyticOnNhd ℂ f (closedBall 0 (2 * ‖w‖)) := h₁f.mono (by tauto)
  convert η₀ h₁w h₃w h₁f using 2
  · field_simp
    ring
  · simp

theorem logCounting_isBigO_one_iff_analyticOnNhd (h₁f : AnalyticOnNhd ℂ f univ) :
    ValueDistribution.proximity f ⊤ =O[atTop] (1 : ℝ → ℝ) ↔ f = fun _ ↦ f 0 := by
  constructor
  · intro h
    have : Bornology.IsBounded (range f) := by
      obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.1 h
      rw [Filter.eventually_atTop] at hc
      obtain ⟨a, ha⟩ := hc
      rw [isBounded_iff_forall_norm_le]
      use c
      intro x hx
      simp at hx



      sorry

    sorry
  · intro h₂f
    rw [h₂f]
    -- should be simp
    rw [ValueDistribution.proximity_top]
    apply Asymptotics.isBigO_iff.2
    use ‖posLog ‖f 0‖‖
    filter_upwards
    intro a
    rw [circleAverage_const]
    simp
