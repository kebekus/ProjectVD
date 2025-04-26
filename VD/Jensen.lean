import Mathlib.Analysis.Complex.Basic
import VD.CircleAverage
import VD.specialFunctions_CircleIntegral_affine
import VD.stronglyMeromorphicOn_eliminate
import VD.Eliminate
import VD.intervalIntegrability

open Filter MeromorphicOn Metric Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




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

@[simp]
theorem Jensen₁
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
  rw [circleAverage_sum this]
  -- Identify summands
  apply Finset.sum_congr rfl
  intro u hu
  simp_rw [← smul_eq_mul]
  rw [circleAverage_smul_fun]
  congr
  apply Jensen₀
  apply D.supportWithinDomain
  simp_all

@[simp]
theorem Jensen₂ {R : ℝ} {g : ℂ → ℂ}
    (h₁g : AnalyticOnNhd ℂ g (closedBall 0 |R|))
    (h₂g : ∀ u : (closedBall (0 : ℂ) |R|), g u ≠ 0) :
    circleAverage (fun x ↦ log ‖g x‖) 0 R = log ‖g 0‖ := by
  apply harmonic_meanValue₂
    (fun x hx ↦ logabs_of_holomorphicAt_is_harmonic (h₁g x hx).holomorphicAt (h₂g ⟨x, hx⟩))

theorem jensenNT {R : ℝ} (hR : R ≠ 0) (f : ℂ → ℂ)
    (h₁f : MeromorphicOn f (closedBall 0 |R|))
    (h₂f : ∀ u : (closedBall (0 : ℂ) |R|), (h₁f u u.2).order ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 |R|)
      ∧ (∀ u : (closedBall (0 : ℂ) |R|), g u ≠ 0)
      ∧ (log ‖f ·‖) =ᶠ[Filter.codiscreteWithin (closedBall 0 |R|)]
        ∑ᶠ u, (divisor f (closedBall (0 : ℂ) |R|) u * log ‖· - u‖) + (log ‖g ·‖)
      ∧ circleAverage (log ‖f ·‖) 0 R
        = ∑ᶠ (i : ℂ), ↑((divisor f (closedBall 0 |R|)) i) * log R + log ‖g 0‖ := by
  -- Decompose f modulo equality on codiscrete sets, extracting zeros and poles
  have h₃f := (divisor f (closedBall 0 |R|)).finiteSupport (isCompact_closedBall 0 |R|)
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.extract_zeros_poles_log h₂f h₃f
  use g, h₁g, h₂g, h₃g
  -- Apply the decomposition of f under the integral
  rw [circleAverage_congr_codiscreteWithin (codiscreteWithin.mono sphere_subset_closedBall h₃g) hR]
  -- Decompose the integral
  have : CircleIntegrable (∑ᶠ i, fun x ↦ (divisor f (closedBall 0 |R|) i) * log ‖x - i‖) 0 R := by
    apply CircleIntegrable.finsum
    intro u
    apply CircleIntegrable.const_mul
    apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm
  rw [circleAverage_add this
    (h₁g.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm]
  -- Identify pieces
  simp [h₁g, h₂g]
