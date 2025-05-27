import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.CircleAverage
import VD.specialFunctions_CircleIntegral_affine
import VD.LeadCoefficientFactorizedRational

open Filter MeromorphicAt MeromorphicOn Metric Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
# Counting Function
-/

/--
Alternate presentation of the finsum that appears in the counting function.
-/
lemma CountingFunction.finsum_eq_finsum_add {R : ℝ} {D : ℂ → ℤ} (hR : R ≠ 0) (hD : D.support.Finite) :
    ∑ᶠ u, (D u) * (log R - log ‖u‖) = ∑ᶠ u, (D u) * log (R * ‖u‖⁻¹) + D 0 * log R := by
  by_cases h : 0 ∈ D.support
  · have {g : ℂ → ℝ} : (fun u ↦ (D u) * (g u)).support ⊆ hD.toFinset := by
      intro x
      contrapose
      simp_all
    simp only [finsum_eq_sum_of_support_subset _ this,
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
