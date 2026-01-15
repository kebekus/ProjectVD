import VD.Cartan
import Mathlib

open Asymptotics Filter Function Metric Real Set Classical Topology ValueDistribution

/-
Prove that the logarithmic counting function of a meromorphic function `f` is
bounded if and only if `f` is constant.

Investigate what happens if the logarithmic counting function grows
symptotically like `log`.
-/

namespace Function.locallyFinsuppWithin

variable
  {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

lemma zero_iff_logCounting_bounded {D : locallyFinsuppWithin (univ : Set E) ℤ} (h : 0 ≤ D) :
    D = 0 ↔ logCounting D =O[atTop] (1 : ℝ → ℝ) := by
  constructor
  · intro h₂
    simp [isBigO_of_le' (c := 0), h₂]
  · contrapose
    intro h₁
    obtain ⟨z, hz⟩ := (by simpa [locallyFinsuppWithin.ext_iff] using h₁ : ∃ z, D z ≠ 0)
    rw [isBigO_iff]
    push_neg
    intro a
    simp
    rw [frequently_atTop]
    intro b
    simp [logCounting]

    sorry

end Function.locallyFinsuppWithin
