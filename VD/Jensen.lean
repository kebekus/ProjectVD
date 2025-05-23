import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.MeasureTheory.Integral.CircleAverage
import VD.specialFunctions_CircleIntegral_affine
import VD.LeadCoefficientFactorizedRational

open Filter MeromorphicAt MeromorphicOn Metric Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
# Circle Integrability
-/

theorem CircleIntegrable.const_mul {c : ℂ} {a R : ℝ} {f : ℂ → ℝ} (h : CircleIntegrable f c R) :
    CircleIntegrable (a • f) c R := by
  apply IntervalIntegrable.const_mul h

theorem CircleIntegrable.const_mul_fun {c : ℂ} {a R : ℝ} {f : ℂ → ℝ} (h : CircleIntegrable f c R) :
    CircleIntegrable (fun z ↦ a * f z) c R := by
  apply CircleIntegrable.const_mul h

/-!
## Circle Averages
-/

theorem circleAverage_logAbs_affine
    {R : ℝ} {c u : ℂ}
    (hu : u ∈ closedBall c |R|) :
    circleAverage (log ‖· - u‖) c R = log R := by
  rw [← circleAverage_fun_add]
  have : (fun z ↦ log ‖z + c - u‖) = (log ‖· - (u - c)‖) := by
    ext z
    congr 2
    ring
  rw [this]
  unfold circleAverage
  by_cases hR : R = 0
  · simp_all
  rw [int₅ hR (by aesop), smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero two_ne_zero pi_ne_zero)]
  ring

@[simp]
theorem circleAverage_logAbs_factorizedRational {R : ℝ} {c : ℂ}
    (D : Function.locallyFinsuppWithin (closedBall c |R|) ℤ) :
    circleAverage (∑ᶠ u, ((D u) * log ‖· - u‖)) c R = ∑ᶠ u, (D u) * log R := by
  -- Turn finsums into sums
  have h := D.finiteSupport (isCompact_closedBall c |R|)
  have : (fun u x ↦ (D u) * log ‖x - u‖).support ⊆ h.toFinset := by
    intro u
    contrapose
    aesop
  simp_rw [finsum_eq_sum_of_support_subset _ this]
  have : (fun u ↦ (D u) * log R).support ⊆ h.toFinset := by
    intro u
    contrapose
    aesop
  simp_rw [finsum_eq_sum_of_support_subset _ this]
  -- Take the sum out of the integral
  have : ∀ i ∈ h.toFinset, CircleIntegrable (fun x ↦ (D i) * log ‖x - i‖) c R := by
    intro u hu
    apply IntervalIntegrable.const_mul
    apply MeromorphicOn.circleIntegrable_log_norm (f := (· - u))
    apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn
  rw [circleAverage_sum this]
  -- Identify summands
  apply Finset.sum_congr rfl
  intro u hu
  simp_rw [← smul_eq_mul, circleAverage_fun_smul]
  congr
  apply circleAverage_logAbs_affine
  apply D.supportWithinDomain
  simp_all

theorem circleIntegrable_logAbs_factorizedRational {R : ℝ} {c : ℂ} (D : ℂ → ℤ) :
    CircleIntegrable (∑ᶠ u, ((D u) * log ‖· - u‖)) c R := by
  apply CircleIntegrable.finsum
  intro u
  apply CircleIntegrable.const_mul
  apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm

-- WARNING: Want that for function to E
@[simp]
theorem circleAverage_nonVanishAnalytic {R : ℝ} {c : ℂ} {g : ℂ → ℂ}
    (h₁g : AnalyticOnNhd ℂ g (closedBall c |R|))
    (h₂g : ∀ u : closedBall c |R|, g u ≠ 0) :
    circleAverage (log ‖g ·‖) c R = log ‖g c‖ := by
  apply harmonic_meanValue₂
    (fun x hx ↦ logabs_of_holomorphicAt_is_harmonic (h₁g x hx).holomorphicAt (h₂g ⟨x, hx⟩))

theorem xx {R : ℝ} {D : ℂ → ℤ} (hR : R ≠ 0) (hD : D.support.Finite) :
    ∑ᶠ u, (D u) * (log R - log ‖u‖) = ∑ᶠ u, (D u) * log (R * ‖u‖⁻¹) + D 0 * log R := by
  by_cases h : 0 ∈ D.support
  · have t₀ {g : ℂ → ℝ} : (fun u ↦ (D u) * (g u)).support ⊆ hD.toFinset := by
      intro x
      contrapose
      simp_all
    simp only [finsum_eq_sum_of_support_subset _ t₀,
      Finset.sum_eq_sum_diff_singleton_add ((Set.Finite.mem_toFinset hD).mpr h), norm_zero,
      log_zero, sub_zero, inv_zero, mul_zero, add_zero, add_left_inj]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset, Function.mem_support, ne_eq,
      Finset.mem_singleton] at hx
    congr
    rw [log_mul hR (inv_ne_zero (norm_ne_zero_iff.mpr hx.2)), log_inv]
    ring
  · simp_all only [ne_eq, Function.mem_support, Decidable.not_not, Int.cast_zero, zero_mul,
      add_zero]
    apply finsum_congr
    intro x
    by_cases h₁ : x = 0
    · simp_all
    · simp only [log_mul hR (inv_ne_zero (norm_ne_zero_iff.mpr h₁)), log_inv, mul_eq_mul_left_iff,
        Int.cast_eq_zero]
      left
      ring

/-!
## Jensen's Formula
-/

-- WARNING: Want that for function to E
theorem JensenFormula {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0) (h₁f : MeromorphicOn f (closedBall 0 |R|))
    (h₂f : ∀ u : closedBall (0 : ℂ) |R|, (h₁f u u.2).order ≠ ⊤) :
    circleAverage (log ‖f ·‖) 0 R
      = ∑ᶠ (u : ℂ), (divisor f (closedBall 0 |R|) u) * log (R * ‖u‖⁻¹)
        + (divisor f (closedBall 0 |R|) 0) * log R + log ‖leadCoefficient f 0‖ := by
  -- Shorthand notation to keep line size in check
  let CB := closedBall (0 : ℂ) |R|
  have h₃f := (divisor f CB).finiteSupport (isCompact_closedBall 0 |R|)
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.extract_zeros_poles h₂f h₃f

  calc circleAverage (log ‖f ·‖) 0 R
  _ = circleAverage ((∑ᶠ u, (divisor f CB u * log ‖· - u‖)) + (log ‖g ·‖)) 0 R := by
    have h₄g := extract_zeros_poles_log h₂g h₃g
    rw [circleAverage_congr_codiscreteWithin (codiscreteWithin.mono sphere_subset_closedBall h₄g) hR]
  _ = circleAverage (∑ᶠ u, (divisor f CB u * log ‖· - u‖)) 0 R + circleAverage (log ‖g ·‖) 0 R := by
    apply circleAverage_add
    exact circleIntegrable_logAbs_factorizedRational (divisor f CB)
    exact (h₁g.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  _ = ∑ᶠ u, divisor f CB u * log R + log ‖g 0‖ := by
    simp [h₁g, h₂g]
  _ = ∑ᶠ u, divisor f CB u * log R + (log ‖leadCoefficient f 0‖ - ∑ᶠ u, divisor f CB u * log ‖u‖) := by
    have t₀ : 0 ∈ CB := by simp [CB]
    have t₁ : CBᶜ ∉ nhdsWithin 0 {0}ᶜ := by
      apply compl_not_mem
      apply mem_nhdsWithin.mpr
      use ball 0 |R|
      simpa [hR] using fun _ ⟨h, _⟩ ↦ ball_subset_closedBall h
    simp [extract_zeros_poles_leadCoefficient_log_norm h₃f t₀ t₁ (h₁f 0 t₀) (h₁g 0 t₀) (h₂g ⟨0, t₀⟩) h₃g]
  _ = ∑ᶠ u, divisor f CB u * log R - ∑ᶠ u, divisor f CB u * log ‖u‖ + log ‖leadCoefficient f 0‖ := by
    ring
  _ = (∑ᶠ u, divisor f CB u * (log R - log ‖u‖)) + log ‖leadCoefficient f 0‖ := by
    rw [← finsum_sub_distrib]
    simp_rw [← mul_sub]
    repeat
      apply h₃f.subset (fun _ ↦ (by simp_all))
  _ = ∑ᶠ u, divisor f CB u * log (R * ‖u‖⁻¹) + divisor f CB 0 * log R + log ‖leadCoefficient f 0‖ := by
    rw [xx hR h₃f]
