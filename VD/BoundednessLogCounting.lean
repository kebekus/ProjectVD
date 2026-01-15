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

lemma elementIndicatorSupport {X : Type*} {e : X} :
    (if · = e then 1 else 0 : X → ℤ).support = {e} := by
  aesop

variable
  {E : Type*} [NormedAddCommGroup E] --[ProperSpace E]

noncomputable def singleton (e : E) :
    Function.locallyFinsuppWithin (Set.univ : Set E) ℤ where
  toFun := fun z ↦ if z = e then 1 else 0
  supportWithinDomain' z hz := by tauto
  supportLocallyFiniteWithinDomain' := by
    intro _ _
    use ⊤
    simp [(by aesop : (if · = e then 1 else 0 : E → ℤ).support = {e})]

lemma xx {e₁ e₂ : E} :
    singleton e₁ e₂ = if e₂ = e₁ then 1 else 0 := by
  have : singleton e₁ e₂ = (singleton e₁).toFun e₂ := rfl
  rw [this]
  unfold singleton
  simp

lemma xxy [ProperSpace E] {e : E} :
    logCounting (singleton e) =O[atTop] log := by
  simp [logCounting]
  rw [isBigO_iff]
  use 2
  rw [eventually_atTop]
  use ‖e‖
  intro b hb

  rw [finsum_eq_sum_of_support_subset _ (s := (finite_singleton e).toFinset)]
  simp
  rw [toClosedBall_eval_within]
  rw [xx]
  simp
  by_cases h : e = 0
  · simp [h, xx]
    sorry
  · simp [xx]
    rw [eq_comm] at h
    simp [h]
    rw [log_mul]

    sorry

  simp [singleton]

  rw [FunLike.coe_injective]
  rw []


  sorry

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
