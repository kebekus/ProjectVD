import Mathlib.Analysis.Meromorphic.FactorizedRational
import VD.specialFunctions_CircleIntegral_affine

open Filter MeromorphicAt MeromorphicOn Metric Real

variable
  {E : Type*} [NormedRing E]

/-!
# Circle Integrability
-/

theorem CircleIntegrable.const_smul {c : ℂ} {R : ℝ} {a : E} {f : ℂ → E} (h : CircleIntegrable f c R) :
    CircleIntegrable (a • f) c R := by
  apply IntervalIntegrable.const_mul h

theorem CircleIntegrable.const_smul_fun {c : ℂ} {R : ℝ} {a : E} {f : ℂ → E} (h : CircleIntegrable f c R) :
    CircleIntegrable (fun z ↦ a • f z) c R := by
  apply CircleIntegrable.const_smul h

theorem circleIntegrable_log_norm_factorizedRational {R : ℝ} {c : ℂ} (D : ℂ → ℤ) :
    CircleIntegrable (∑ᶠ u, ((D u) * log ‖· - u‖)) c R :=
  CircleIntegrable.finsum (fun _ ↦ (circleIntegrable_log_norm_meromorphicOn
    (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn).const_smul)
