import Mathlib.Analysis.Complex.Basic
import VD.specialFunctions_CircleIntegral_affine
import VD.stronglyMeromorphicOn_eliminate
import VD.Eliminate

open Filter MeromorphicOn Metric Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


/-!
# Circle Averages
-/

noncomputable def circleAverage (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
  (2 * π)⁻¹ • ∫ θ : ℝ in (0)..2 * π, f (circleMap c R θ)

theorem circleAverage_congr_codiscreteWithin {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℝ}
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R ≠ 0) :
    circleAverage f₁ c R = circleAverage f₂ c R := by
  unfold circleAverage
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  apply codiscreteWithin.mono (by tauto) (circleMap_preimage_codiscrete hR hf)

theorem circleAverage.average_finset_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ → E}
    {c : ℂ} {R : ℝ} (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    circleAverage (∑ i ∈ s, f i) c R = ∑ i ∈ s, circleAverage (f i) c R := by
  unfold circleAverage
  simp [← Finset.smul_sum, intervalIntegral.integral_finset_sum h]

theorem CircleAverage.const_smul {c : ℂ} {a R : ℝ} {f : ℂ → E} :
    circleAverage (a • f) c R = a • circleAverage f c R := by
  unfold circleAverage
  rw [smul_comm]
  congr
  exact intervalIntegral.integral_smul a fun x ↦ f (circleMap c R x)

theorem CircleAverage.const_smul_fun {c : ℂ} {a R : ℝ} {f : ℂ → E} :
    circleAverage (fun z ↦ a • f z) c R = a • circleAverage f c R := by
  apply CircleAverage.const_smul

theorem circleAverage.average_add {f g : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    circleAverage (f + g) c R = circleAverage f c R + circleAverage g c R := by
  sorry


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
# Decomposition
-/

theorem Jensen₀
    {R : ℝ} {u : ℂ}
    (hu : u ∈ closedBall 0 |R|) :
    circleAverage (log ‖· - u‖) 0 R = log R := by
  unfold circleAverage
  by_cases hR : R = 0
  · simp_all
  rw [int₅ hR hu, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero two_ne_zero pi_ne_zero)]
  ring

@[simp] theorem Jensen₁
    {R : ℝ}
    (D : Function.locallyFinsuppWithin (closedBall (0 : ℂ) |R|) ℤ) :
    circleAverage (∑ᶠ u, fun z ↦ (D u) * log ‖z - u‖) 0 R = ∑ᶠ u, (D u) * log R := by
  -- Turn finsums into sums
  have h := D.finiteSupport (isCompact_closedBall 0 |R|)
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
  have : ∀ i ∈ h.toFinset, CircleIntegrable (fun x ↦ (D i) * log ‖x - i‖) 0 R := by
    intro u hu
    apply IntervalIntegrable.const_mul
    apply MeromorphicOn.circleIntegrable_log_norm (f := (· - u))
    apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn
  rw [circleAverage.average_finset_sum this]
  -- Identify summands
  apply Finset.sum_congr rfl
  intro u hu
  simp_rw [← smul_eq_mul]
  rw [CircleAverage.const_smul_fun]
  congr
  apply Jensen₀
  apply D.supportWithinDomain
  simp_all

@[simp] theorem Jensen₂
    {R : ℝ}
    {g : ℂ → ℂ}
    (h₁g : AnalyticOnNhd ℂ g (closedBall 0 |R|))
    (h₂g : ∀ u : (closedBall (0 : ℂ) |R|), g u ≠ 0) :
    circleAverage (fun x ↦ log ‖g x‖) 0 |R| = log ‖g 0‖ := by
  unfold circleAverage
  by_cases hR : R = 0
  · simp only [hR, abs_zero, circleMap_zero_radius, Function.const_apply,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero two_ne_zero pi_ne_zero)]
    simp

  rw [harmonic_meanValue₁ |R| (abs_pos.mpr hR)
    (fun x hx ↦ logabs_of_holomorphicAt_is_harmonic (h₁g x hx).holomorphicAt (h₂g ⟨x, hx⟩))]
  rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero two_ne_zero pi_ne_zero)]
  simp



theorem jensenNT {R : ℝ} (hR : R ≠ 0)
    (f : ℂ → ℂ)
    (h₁f : MeromorphicNFOn f (closedBall 0 |R|))
    (h₂f : ∀ u : (closedBall (0 : ℂ) |R|), (h₁f u.2).meromorphicAt.order ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 |R|)
      ∧ (∀ u : (closedBall (0 : ℂ) |R|), g u ≠ 0)
      ∧ (log ‖f ·‖) =ᶠ[Filter.codiscreteWithin (closedBall 0 |R|)]
        ∑ᶠ u, (divisor f (closedBall (0 : ℂ) |R|) u * log ‖· - u‖) + (log ‖g ·‖)
      ∧ circleAverage (log ‖f ·‖) 0 R
        = ∑ᶠ (i : ℂ), ↑((divisor f (closedBall 0 |R|)) i) * log R + log ‖g 0‖ := by
  -- Decompose f modulo equality on codiscrete sets, extracting zeros and poles
  have h₃f := (divisor f (closedBall 0 |R|)).finiteSupport (isCompact_closedBall 0 |R|)
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.meromorphicOn.extract_zeros_poles_log h₂f h₃f
  use g, h₁g, h₂g, h₃g
  -- Apply the decomposition of f under the integral
  rw [circleAverage_congr_codiscreteWithin (codiscreteWithin.mono sphere_subset_closedBall h₃g) hR]
  -- Decompose the integral
  have : CircleIntegrable (∑ᶠ i, fun x ↦ (divisor f (closedBall 0 |R|) i) * log ‖x - i‖) 0 R := by
    apply CircleIntegrable.finsum
    intro u
    apply CircleIntegrable.const_mul
    apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm
  rw [circleAverage.average_add this
    (h₁g.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm]
  -- Identify pieces
  simp [h₁g, h₂g]

  apply Jensen₂ h₁g


  apply Jensen₂ h₁g h₂g
  unfold circleAverage
  simp
  rw [harmonic_meanValue₁ (f := (log ‖g ·‖))]

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
