import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.Complex.ValueDistribution.ProximityFunction
import Mathlib.RingTheory.LocalRing.Basic
import VD.MathlibSubmitted.DivisorOrder

open MeromorphicOn Metric Real Set Classical Function.locallyFinsuppWithin

namespace ValueDistribution


@[simp] lemma posLog_zero : log⁺ 0 = 0 := by simp [posLog]

@[simp] lemma posLog_one : log⁺ 1 = 0 := by simp [posLog]

@[simp] lemma posLog_pow {n : ℕ} {a : ℝ} :
    log⁺ (a ^ n) = n * log⁺ a := by
  by_cases hn : n = 0
  · simp_all
  by_cases h₂a : |a| ≤ 1
  · simp_all [pow_le_one₀, (posLog_eq_zero_iff _).2]
  rw [not_le] at h₂a
  have : 1 < |a ^ n| := by simp [one_lt_pow₀ h₂a hn]
  simp [posLog_eq_log this.le, posLog_eq_log h₂a.le]

@[simp] theorem proximity_pow_zero {f : ℂ → ℂ} {n : ℕ} (hf : MeromorphicOn f Set.univ) :
    proximity (f ^ n) 0 = n • (proximity (f ^ n) 0) := by
  simp [proximity]
  sorry

/--
For natural numbers `n`, the counting function counting poles of `f ^ n` equals
`n` times the counting function counting poles of `f`.
-/
@[simp] theorem proximity_pow_top {f : ℂ → ℂ} {n : ℕ} (hf : MeromorphicOn f Set.univ) :
    proximity (f ^ n) ⊤ = n • (proximity (f ^ n) ⊤) := by
  simp [proximity]
  have {a : ℝ} : log⁺ (a ^ n) = n * log⁺ a := by
    sorry
  sorry

end ValueDistribution
