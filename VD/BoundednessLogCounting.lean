import VD.Cartan
import Mathlib

open Asymptotics Filter Function Metric Real Set Classical Topology ValueDistribution

/-
Prove that the logarithmic counting function of a meromorphic function `f` is
bounded if and only if `f` is constant.

Investigate what happens if the logarithmic counting function grows
symptotically like `log`. f : ℂ → ℂ
-/

namespace Function.locallyFinsuppWithin

lemma elementIndicatorSupport {X : Type*} {e : X} :
    (if · = e then 1 else 0 : X → ℤ).support = {e} := by
  aesop

variable
  {E : Type*} [NormedAddCommGroup E] --[ProperSpace E]

noncomputable def single (e : E) :
    Function.locallyFinsuppWithin (Set.univ : Set E) ℤ where
  toFun := (if · = e then 1 else 0)
  supportWithinDomain' z hz := by tauto
  supportLocallyFiniteWithinDomain' := by
    intro _ _
    use ⊤
    simp [(by aesop : (if · = e then 1 else 0 : E → ℤ).support = {e})]

lemma single_eval {e₁ e₂ : E} :
    single e₁ e₂ = if e₂ = e₁ then 1 else 0 := by
  have : single e₁ e₂ = (single e₁).toFun e₂ := rfl
  rw [this]
  unfold single
  simp

lemma logCounting_single [ProperSpace E] {e : E} {r : ℝ} (hr : ‖e‖ ≤ r) :
    logCounting (single e) r = log (r * ‖e‖⁻¹) + ↑((single e) 0) * log r := by
  simp [logCounting]
  rw [finsum_eq_sum_of_support_subset _ (s := (finite_singleton e).toFinset)]
  simp
  rw [toClosedBall_eval_within]
  rw [single_eval]
  simp
  · simp
    have : 0 ≤ r := by
      trans ‖e‖
      · exact norm_nonneg e
      · exact hr
    rwa [abs_of_nonneg this]
  · intro y hy
    simp_all
    have h₁y := hy.left
    simp [toClosedBall, restrict_apply, single_eval] at h₁y
    tauto

lemma logCounting_single_zero [ProperSpace E] {r : ℝ} (hr : 0 ≤ r) :
    logCounting (single (0 : E)) r = log r := by
  rw [logCounting_single]
  simp_all [single_eval]
  simpa

lemma logCounting_single_nonzero [ProperSpace E] {e : E} {r : ℝ} (hr : ‖e‖ ≤ r) :
    logCounting (single e) r = log r - log ‖e‖ := by
  rw [logCounting_single]
  by_cases he : 0 = e
  · simp [← he, single_eval]
  simp_all [single_eval]
  rw [log_mul, log_inv]
  ring
  · have h₁ : ‖e‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr fun a ↦ he (id (Eq.symm a))
    have h₂ : 0 < ‖e‖ := by
      exact norm_pos_iff.mpr fun a ↦ he (id (Eq.symm a))
    have h₃ : 0 < r := by
      exact Std.lt_of_lt_of_le h₂ hr
    exact Ne.symm (ne_of_lt h₃)
  · have h₁ : ‖e‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr fun a ↦ he (id (Eq.symm a))
    exact inv_ne_zero h₁
  · exact hr

lemma logCounting_single_isBigO_log [ProperSpace E] {e : E} :
    logCounting (single e) =O[atTop] log := by
  simp [logCounting]
  rw [isBigO_iff]
  use 2
  rw [eventually_atTop]
  use Real.exp |log ‖e‖|
  intro b hb
  have h₁b : 0 < b := by
    have := Real.exp_pos |log ‖e‖|
    linarith
  have h₂b : 1 ≤ b := by
    trans Real.exp |log ‖e‖|
    · apply Real.one_le_exp
      exact abs_nonneg (log ‖e‖)
    · exact hb
  rw [finsum_eq_sum_of_support_subset _ (s := (finite_singleton e).toFinset)]
  simp
  rw [toClosedBall_eval_within]
  rw [single_eval]
  simp
  by_cases h : e = 0
  · simp [h, single_eval]
    grind
  · simp [single_eval]
    rw [eq_comm] at h
    simp [h]
    rw [log_mul]
    calc |log b + log ‖e‖⁻¹|
      _ ≤ |log b| + |log ‖e‖⁻¹| := by
        apply abs_add_le
      _ ≤ |log b| + |log ‖e‖| := by
        simp [log_inv]
      _ ≤ |log b| + |log b| := by
        gcongr 1
        have := log_le_log (Real.exp_pos |log ‖e‖|) hb
        simp at this
        have : 0 ≤ log b := by
          exact log_nonneg h₂b
        have : log b = |log b| := by
          exact Eq.symm (abs_of_nonneg this)
        rwa [← this]
      _ = 2 * |log b| := by
        rw [two_mul]
    · exact Ne.symm (ne_of_lt h₁b)
    · aesop

  · simp
    have := log_le_log (Real.exp_pos |log ‖e‖|) hb
    simp at this
    by_cases he : e = 0
    · simp [he]
    rw [← log_le_log_iff]
    simp_all only [ge_iff_le, log_abs]
    by_cases he : 0 ≤ log ‖e‖
    · rwa [abs_of_nonneg he] at this
    · trans 0
      · linarith
      · exact log_nonneg h₂b
    aesop
    rwa [abs_of_pos h₁b]
  intro y hy
  simp_all
  have h₁y := hy.left
  simp [toClosedBall, restrict_apply, single_eval] at h₁y
  tauto

lemma xx [ProperSpace E] {D : locallyFinsuppWithin (univ : Set E) ℤ}
    (h₁ : 0 ≤ D) (h₂ : D ≠ 0) :
    ∃ e, single e ≤ D := by
  obtain ⟨z, hz⟩ := (by simpa [locallyFinsuppWithin.ext_iff] using h₂ : ∃ z, D z ≠ 0)
  use z
  intro e
  simp [single_eval]
  by_cases he : e = z
  · simp [he]
    have : 1 ≤ D e := by
      have := h₁ e
      simp_all
      have : 0 < D e := by
        refine Int.lt_iff_le_and_ne.mpr ?_
        simp_all
        tauto
      aesop
    aesop
  aesop

lemma zero_iff_logCounting_bounded [ProperSpace E] {D : locallyFinsuppWithin (univ : Set E) ℤ}
    (h : 0 ≤ D) :
    D = 0 ↔ logCounting D =O[atTop] (1 : ℝ → ℝ) := by
  constructor
  · intro h₂
    simp [isBigO_of_le' (c := 0), h₂]
  · contrapose
    intro h₁
    obtain ⟨e, he⟩ := xx h h₁
    rw [isBigO_iff]
    push_neg
    intro a
    simp
    rw [frequently_atTop]
    intro b

    --simp [logCounting]

    sorry

end Function.locallyFinsuppWithin
