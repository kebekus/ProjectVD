import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import VD.MathlibPending.Single

open Asymptotics Filter Function Real Set Classical

namespace Function.locallyFinsuppWithin

variable
  {E : Type*} [NormedAddCommGroup E]  [ProperSpace E]

/-!
## Logarithmic Counting Functions of Singleton Indicators
-/

/--
The logarithmic counting function of a singleton indicator is asymptotically
equal to `log · - log ‖e‖`.
-/
@[simp] lemma logCounting_single_eq_log_sub_const {e : E} {r : ℝ} (hr : ‖e‖ ≤ r) :
    logCounting (single e) r = log r - log ‖e‖ := by
  simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset _ (s := (finite_singleton e).toFinset)
    (by simp_all [toClosedBall, restrict_apply, single_eval])]
  simp only [toFinite_toFinset, toFinset_singleton, Finset.sum_singleton]
  rw [toClosedBall_eval_within _ (by simpa [abs_of_nonneg ((norm_nonneg e).trans hr)])]
  by_cases he : 0 = e
  · simp [← he, single_eval]
  · simp only [single_eval, he, reduceIte, Int.cast_zero, zero_mul, add_zero,
      log_mul (ne_of_lt (lt_of_lt_of_le (norm_pos_iff.mpr (he ·.symm)) hr)).symm
      (inv_ne_zero (norm_ne_zero_iff.mpr (he ·.symm))), log_inv]
    ring

/-!
## Monotonicity of Logarithmic Counting Functions
-/

/--
The logarithmic counting function of a positive function is locally finite
support is asymptotically strictly monotone.
-/
lemma logCounting_strictMono {D : locallyFinsuppWithin (univ : Set E) ℤ} {e : E}
    (hD : single e ≤ D) :
    StrictMonoOn (logCounting D) (Ioi ‖e‖) := by
  rw [(by aesop : logCounting D = logCounting (single e) + logCounting (D - single e))]
  apply StrictMonoOn.add_monotone
  · intro a ha b hb hab
    rw [mem_Ioi] at ha hb
    rw [logCounting_single_eq_log_sub_const ha.le, logCounting_single_eq_log_sub_const hb.le]
    gcongr
    exact (norm_nonneg e).trans_lt ha
  · intro a ha b hb hab
    apply logCounting_mono _ _ ((norm_nonneg e).trans_lt hb) hab
    · simp [hD]
    · simpa [mem_Ioi] using (norm_nonneg e).trans_lt ha

end Function.locallyFinsuppWithin
