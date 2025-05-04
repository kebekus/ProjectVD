import Mathlib.Analysis.Complex.Basic
import VD.ToMathlib.CircleAverage
import VD.specialFunctions_CircleIntegral_affine
--import VD.stronglyMeromorphicOn_eliminate
import VD.ToMathlib.Eliminate
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
## Circle Averages
-/

theorem circleAverage_logAbs_affine
    {R : ℝ} {c u : ℂ}
    (hu : u ∈ closedBall c |R|) :
    circleAverage (log ‖· - u‖) c R = log R := by
  rw [circleAverage_shiftCenter]
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
  simp_rw [← smul_eq_mul]
  rw [circleAverage_smul_fun]
  congr
  apply circleAverage_logAbs_affine
  apply D.supportWithinDomain
  simp_all

theorem circleIntegrable_logAbs_factorizedRational {R : ℝ} {c : ℂ}
    (D : Function.locallyFinsuppWithin (closedBall c |R|) ℤ) :
    CircleIntegrable (∑ᶠ u, ((D u) * log ‖· - u‖)) c R := by
  apply CircleIntegrable.finsum
  intro u
  apply CircleIntegrable.const_mul
  apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm

@[simp]
theorem circleAverage_nonVanishAnalytic {R : ℝ} {c : ℂ} {g : ℂ → ℂ}
    (h₁g : AnalyticOnNhd ℂ g (closedBall c |R|))
    (h₂g : ∀ u : closedBall c |R|, g u ≠ 0) :
    circleAverage (log ‖g ·‖) c R = log ‖g c‖ := by
  apply harmonic_meanValue₂
    (fun x hx ↦ logabs_of_holomorphicAt_is_harmonic (h₁g x hx).holomorphicAt (h₂g ⟨x, hx⟩))

/-!
## Jensen's Formula
-/
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
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.extract_zeros_poles h₂f h₃f
  have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
  use g, h₁g, h₂g, h₄g
  -- Apply the decomposition of f under the integral
  rw [circleAverage_congr_codiscreteWithin (codiscreteWithin.mono sphere_subset_closedBall h₄g) hR]
  -- Decompose the integral
  rw [circleAverage_add (circleIntegrable_logAbs_factorizedRational (divisor f (closedBall 0 |R|)))
    (h₁g.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm]
  -- Identify pieces
  simp [h₁g, h₂g]
