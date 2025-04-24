import VD.specialFunctions_CircleIntegral_affine
import VD.stronglyMeromorphicOn_eliminate
import VD.Eliminate

open Filter MeromorphicOn Metric Real


theorem circleAverage_congr_codiscreteWithin {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℝ}
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R ≠ 0) :
    (∫ x in (0)..(2 * π), f₁ (circleMap c R x)) = (∫ x in (0)..(2 * π), f₂ (circleMap c R x)) := by
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  apply codiscreteWithin.mono (by tauto) (circleMap_preimage_codiscrete hR hf)

theorem CircleIntegrable.const_mul {c : ℂ} {a R : ℝ} {f : ℂ → ℝ} (h : CircleIntegrable f c R) :
    CircleIntegrable (a • f) c R := by
  apply IntervalIntegrable.const_mul h

theorem CircleIntegrable.const_mul_fun {c : ℂ} {a R : ℝ} {f : ℂ → ℝ} (h : CircleIntegrable f c R) :
    CircleIntegrable (fun z ↦ a * f z) c R := by
  apply CircleIntegrable.const_mul h

theorem jensenNT {R : ℝ}
    (hR : R ≠ 0)
    (f : ℂ → ℂ)
    (h₁f : MeromorphicNFOn f (closedBall 0 |R|))
    (h₂f : ∀ u : (closedBall (0 : ℂ) |R|), (h₁f u.2).meromorphicAt.order ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 |R|)
      ∧ (∀ u : (closedBall (0 : ℂ) |R|), g u ≠ 0)
      ∧ (log ‖f ·‖) =ᶠ[Filter.codiscreteWithin (closedBall 0 |R|)]
        ∑ᶠ u, (divisor f (closedBall (0 : ℂ) |R|) u * log ‖· - u‖) + (log ‖g ·‖)
      ∧ ⨍ (x : ℝ) in (0)..(2 * π), log ‖f (circleMap 0 R x)‖
        = ∑ᶠ (i : ℂ), ↑((divisor f (closedBall 0 |R|)) i) * log R + log ‖g 0‖ := by
  -- Decompose f modulo equality on codiscrete sets, extracting zeros and poles
  have h₃f := (divisor f (closedBall 0 |R|)).finiteSupport (isCompact_closedBall 0 |R|)
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.meromorphicOn.extract_zeros_poles_log h₂f h₃f
  use g, h₁g, h₂g, h₃g
  -- Apply the decomposition of f under the integral
  rw [interval_average_eq]
  rw [circleAverage_congr_codiscreteWithin (codiscreteWithin.mono sphere_subset_closedBall h₃g) hR]
  rw [← interval_average_eq]
  -- Turn all finsums into sums
  rw [interval_average_eq]
  have : (fun u x ↦ (divisor f (closedBall 0 |R|) u) * log ‖x - u‖).support ⊆ h₃f.toFinset := by
    intro u
    contrapose
    aesop
  rw [finsum_eq_sum_of_support_subset _ this]
  clear this
  have : (fun u ↦ (divisor f (closedBall 0 |R|) u) * log R).support ⊆ h₃f.toFinset := by
    intro u
    contrapose
    aesop
  rw [finsum_eq_sum_of_support_subset _ this]
  clear this
  -- Decompose the integral
  simp_rw [Pi.add_apply]
  have : IntervalIntegrable (fun x ↦ (∑ i ∈ h₃f.toFinset, fun x ↦ ↑((divisor f (closedBall 0 |R|)) i) * log ‖x - i‖) (circleMap 0 R x))
    MeasureTheory.volume 0 (2 * π) := by
    apply CircleIntegrable.sum
    intro u hu
    apply CircleIntegrable.const_mul
    apply MeromorphicOn.circleIntegrable_log_norm
    apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn
  rw [intervalIntegral.integral_add this (h₁g.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm]
  clear this
  -- Further decompose the integral
  simp only [Finset.sum_apply]
  have : ∀ i ∈ h₃f.toFinset, IntervalIntegrable (fun x ↦ ↑((divisor f (closedBall 0 |R|)) i) * log ‖circleMap 0 R x - i‖) MeasureTheory.volume 0 (2 * π) := by
    intro u hu
    apply IntervalIntegrable.const_mul
    apply MeromorphicOn.circleIntegrable_log_norm (f := (· - u))
    apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn
  rw [intervalIntegral.integral_finset_sum this]
  clear this
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul, mul_add]
  -- Identify integrals
  have : ∑ x ∈ h₃f.toFinset, ((divisor f (closedBall 0 |R|)) x) * ∫ (x_1 : ℝ) in (0)..(2 * π), log ‖circleMap 0 R x_1 - x‖
    = ∑ x ∈ h₃f.toFinset, ↑((divisor f (closedBall 0 |R|)) x) * (2 * π) * log R := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [int₅ hR]
    ring
    let A := (divisor f (closedBall 0 |R|)).supportWithinDomain
    have : u ∈ (divisor f (closedBall 0 |R|)).support := by
      simp_all
    exact A this
  rw [this]
  clear this

  -- Identify integral
  have : (⨍ (x : ℝ) in (0)..2 * Real.pi, log ‖g (circleMap 0 R x)‖) = log ‖g 0‖ := by
    apply harmonic_meanValue₂ (f := (log ‖g ·‖))
    exact fun z hz ↦ logabs_of_holomorphicAt_is_harmonic (h₁g z hz).holomorphicAt (h₂g ⟨z, hz⟩)

  nth_rw 4 [← smul_eq_mul]
  rw [← interval_average_eq]
  rw [this]
  clear this
  -- Simplify
  have {a b₁ b₂ c : ℝ} : a * (b₁ * b₂) * c = (b₁ * b₂) * (a * c) := by ring
  simp_rw [this]
  rw [← Finset.mul_sum (a := (2 * π))]
  rw [← mul_assoc]
  have : (2 * π - 0)⁻¹ * (2 * π) = 1 := by
    rw [sub_zero, inv_mul_cancel₀]
    apply mul_ne_zero two_ne_zero pi_ne_zero
  rw [this]
  simp
