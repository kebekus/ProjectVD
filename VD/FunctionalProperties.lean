import VD.Cartan
import Mathlib

open Function Metric Real Set Classical Topology ValueDistribution

/-
Establish parity and monotonocity of the Nevanlinna functions.
-/

namespace Function.locallyFinsuppWithin

variable
  {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/--
The logarithmic counting function is even.
-/
lemma logCounting_even (D : locallyFinsuppWithin (univ : Set E) ℤ) :
    (logCounting D).Even := fun r ↦ by simp [logCounting, toClosedBall, restrict_apply]

lemma toClosedBall_support_subset_closedBall {E : Type*} [NormedAddCommGroup E] {r : ℝ}
    (f : locallyFinsuppWithin (univ : Set E) ℤ) :
    (toClosedBall r f).support ⊆ closedBall 0 |r| := by
  simp_all [toClosedBall, restrict_apply]

/--
The logarithmic counting function is monotonous.
-/
lemma logCounting_mono {D : locallyFinsuppWithin (univ : Set E) ℤ} (hD : 0 ≤ D) :
    MonotoneOn (logCounting D) (Ioi 0) := by
  intro a ha b hb _
  simp_all only [mem_Ioi, logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  gcongr
  · let s := (toClosedBall b D).support
    have hs : s.Finite := (toClosedBall b D).finiteSupport (isCompact_closedBall 0 |b|)
    rw [finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    rw [finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · gcongr 1 with z hz
      by_cases h₂z : z = 0
      · simp [h₂z]
      · have := (toClosedBall_support_subset_closedBall D (hs.mem_toFinset.1 hz))
        rw [toClosedBall_eval_within _ this]
        by_cases h₃z : z ∈ closedBall 0 |a|
        · rw [toClosedBall_eval_within _ h₃z]
          gcongr
          exact Int.cast_nonneg (hD z)
        · simp only [h₃z, not_false_eq_true, apply_eq_zero_of_notMem, Int.cast_zero, zero_mul,
            ge_iff_le]
          apply mul_nonneg (Int.cast_nonneg (hD z)) (log_nonneg _)
          apply (le_mul_inv_iff₀ (norm_pos_iff.mpr h₂z)).2
          simp_all [abs_of_pos hb]
    · intro z
      aesop
    · intro z
      simp only [support_mul, mem_inter_iff, mem_support, ne_eq, Int.cast_eq_zero, log_eq_zero,
        mul_eq_zero, inv_eq_zero, norm_eq_zero, not_or, Finite.coe_toFinset, and_imp, s]
      intro h₁ _ _ _ _
      have : z ∈ closedBall 0 |a| := mem_of_indicator_ne_zero h₁
      rw [toClosedBall_eval_within _ this] at h₁
      rwa [toClosedBall_eval_within]
      · simp_all only [abs_of_pos ha, mem_closedBall, dist_zero_right, abs_of_pos hb]
        linarith
  · exact Int.cast_nonneg (hD 0)

end Function.locallyFinsuppWithin

namespace ValueDistribution

/--
The logarithmic counting function is even.
-/
theorem logCounting_even {f : ℂ → ℂ} {a : WithTop ℂ} :
    Function.Even (logCounting f a) := by
  intro r
  by_cases h : a = ⊤
  all_goals simp [logCounting, h, Function.locallyFinsuppWithin.logCounting_even _ r]

/--
The proximity function is even.
-/
theorem proximity_even {f : ℂ → ℂ} {a : WithTop ℂ} :
    Function.Even (proximity f a) := by
  intro r
  by_cases h : a = ⊤
  all_goals simp [proximity, h]

/--
The characteristic function is even.
-/
theorem characteristic_even {f : ℂ → ℂ} {a : WithTop ℂ} :
    Function.Even (characteristic f a) :=
  Function.Even.add proximity_even logCounting_even

/--
The logarithmic counting function is monotonous.
-/
theorem logCounting_monotoneOn {f : ℂ → ℂ} {a : WithTop ℂ} :
    MonotoneOn (logCounting f a) (Ioi 0) := by
  unfold logCounting
  by_cases h : a = ⊤
  · simp [h]
    apply locallyFinsuppWithin.logCounting_mono (negPart_nonneg _)
  · simp [h]
    apply locallyFinsuppWithin.logCounting_mono (posPart_nonneg _)

/--
The characteristic function is monotonous.
-/
theorem characteristic_monotoneOn {f : ℂ → ℂ} (h : Meromorphic f) :
    MonotoneOn (characteristic f ⊤) (Ioi 0) := by
  obtain ⟨c, hc⟩ := characteristic_top_eq_circleAverage_logCounting_add_const h
  intro a ha b hb hab
  rw [hc a, hc b]
  gcongr
  · apply logCounting_circleIntegrable h
  · apply logCounting_circleIntegrable h
  · apply logCounting_monotoneOn ha hb hab
  · aesop
  · aesop

end ValueDistribution
