import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Complex.CauchyIntegral
import VD.holomorphic_examples

theorem harmonic_meanValue
  {f : ℂ → ℝ}
  {z : ℂ}
  (ρ R : ℝ)
  (hR : 0 < R)
  (hρ : R < ρ)
  (hf : ∀ x ∈ Metric.ball z ρ , HarmonicAt f x) :
  (∫ (x : ℝ) in (0)..2 * Real.pi, f (circleMap z R x)) = 2 * Real.pi * f z
  := by

  obtain ⟨F, h₁F, h₂F⟩ := harmonic_is_realOfHolomorphic (gt_trans hρ hR) hf

  have hrρ : Metric.ball z R ⊆ Metric.ball z ρ := by
    intro x hx
    exact gt_trans hρ hx

  have reg₀F : DifferentiableOn ℂ F (Metric.ball z ρ) :=
    fun x hx ↦ (h₁F x hx).differentiableAt.differentiableWithinAt

  have reg₁F : DifferentiableOn ℂ F (Metric.ball z R) := by
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply HolomorphicAt.differentiableAt (h₁F x _)
    exact hrρ hx

  have : (∮ (x : ℂ) in C(z, R), (x - z)⁻¹ • F x) = (2 * ↑Real.pi * Complex.I) • F z := by
    let s : Set ℂ := ∅
    let hs : s.Countable := Set.countable_empty
    let _ : ℂ := 0
    have hw : (z : ℂ) ∈ Metric.ball z R := Metric.mem_ball_self hR
    have hc : ContinuousOn F (Metric.closedBall z R) := by
      apply reg₀F.continuousOn.mono
      intro x hx
      simp at hx
      simp
      linarith
    have hd : ∀ x ∈ Metric.ball z R \ s, DifferentiableAt ℂ F x := by
      intro x hx
      let A := reg₁F x hx.1
      apply A.differentiableAt
      apply (IsOpen.mem_nhds_iff ?hs).mpr
      exact hx.1
      exact Metric.isOpen_ball
    let CIF := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable hs hw hc hd
    simp at CIF
    assumption

  unfold circleIntegral at this
  simp_rw [deriv_circleMap] at this

  have t₁ {θ : ℝ} : (circleMap 0 R θ * Complex.I) • (circleMap 0 R θ)⁻¹ • F (circleMap z R θ) = Complex.I • F (circleMap z R θ) := by
    rw [← smul_assoc]
    congr 1
    simp
    nth_rw 1 [mul_comm]
    rw [← mul_assoc]
    simp
    apply inv_mul_cancel₀
    apply circleMap_ne_center
    exact hR.ne.symm
  have t'₁  {θ : ℝ} : circleMap 0 R θ = circleMap z R θ - z := by
    exact Eq.symm (circleMap_sub_center z R θ)
  simp_rw [← t'₁, t₁] at this
  simp at this

  have t₂ : Complex.reCLM (-Complex.I * (Complex.I * ∫ (x : ℝ) in (0)..2 * Real.pi, F (circleMap z R x))) = Complex.reCLM (-Complex.I * (2 * ↑Real.pi * Complex.I * F z)) := by
    rw [this]
  simp at t₂
  have xx {x : ℝ} : (F (circleMap z R x)).re = f (circleMap z R x) := by
    rw [← h₂F]
    simp
    simp
    rw [Complex.dist_eq]
    rw [circleMap_sub_center]
    simp
    rwa [abs_of_nonneg hR.le]
  have x₁ {z : ℂ} : z.re = Complex.reCLM z := by rfl
  rw [x₁] at t₂
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm] at t₂
  simp at t₂
  simp_rw [xx] at t₂
  have x₁ {z : ℂ} : z.re = Complex.reCLM z := by rfl
  rw [x₁] at t₂
  have : Complex.reCLM (F z) = f z := by
    apply h₂F
    simp
    exact gt_trans hρ hR
  rw [this] at t₂
  exact t₂

  -- IntervalIntegrable (fun x => F (circleMap 0 1 x)) MeasureTheory.volume 0 (2 * Real.pi)
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.comp reg₀F.continuousOn _
  intro θ _
  simp
  rw [Complex.dist_eq, circleMap_sub_center]
  simp
  rwa [abs_of_nonneg hR.le]
  apply Continuous.continuousOn
  exact continuous_circleMap z R

/- Probably not optimal yet. We want a statements that requires harmonicity in
the interior and continuity on the closed ball.
-/


theorem harmonic_meanValue₁
  {f : ℂ → ℝ}
  {z : ℂ}
  (R : ℝ)
  (hR : 0 < R)
  (hf : ∀ x ∈ Metric.closedBall z R , HarmonicAt f x) :
  (∫ (x : ℝ) in (0)..2 * Real.pi, f (circleMap z R x)) = 2 * Real.pi * f z := by

  obtain ⟨e, h₁e, h₂e⟩ := IsCompact.exists_thickening_subset_open (isCompact_closedBall z R) (HarmonicAt_isOpen f) hf
  rw [thickening_closedBall] at h₂e
  apply harmonic_meanValue (e + R) R
  assumption
  norm_num
  assumption
  exact fun x a => h₂e a
  assumption
  linarith
