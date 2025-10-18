import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open Real

@[simp] lemma posLog_zero : log⁺ 0 = 0 := by simp [posLog]

@[simp] lemma posLog_one : log⁺ 1 = 0 := by simp [posLog]

/--
The positive part of the logarithm commutes with taking powers.
-/
@[simp] lemma posLog_pow {n : ℕ} {a : ℝ} :
    log⁺ (a ^ n) = n * log⁺ a := by
  by_cases hn : n = 0
  · simp_all
  by_cases h₂a : |a| ≤ 1
  · simp_all [pow_le_one₀, (posLog_eq_zero_iff _).2]
  rw [not_le] at h₂a
  have : 1 < |a ^ n| := by simp [one_lt_pow₀ h₂a hn]
  simp [posLog_eq_log this.le, posLog_eq_log h₂a.le]

/--
Variant of `posLog_sum` for norms of elements in normed additive commutative
groups, using monotonicity of `log⁺` and the triangle inequality.
-/
lemma posLog_norm_sum_le {E : Type*} [NormedAddCommGroup E]
    {α : Type*} (s : Finset α) (f : α → E) :
    log⁺ ‖∑ t ∈ s, f t‖ ≤ log s.card + ∑ t ∈ s, log⁺ ‖f t‖ := by
  calc log⁺ ‖∑ t ∈ s, f t‖
  _ ≤ log⁺ (∑ t ∈ s, ‖f t‖) := by
    apply monotoneOn_posLog (by simp) _ (norm_sum_le s f)
    simp [Finset.sum_nonneg (fun i _ ↦ norm_nonneg (f i))]
  _ ≤ log s.card + ∑ t ∈ s, log⁺ ‖f t‖ :=
    posLog_sum s (‖f ·‖)
