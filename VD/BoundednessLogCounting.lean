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
    single e₁ e₂ = if e₂ = e₁ then 1 else 0 := rfl

lemma single_nonneg {e : E} :
    0 ≤ single e := by
  intro x
  by_cases he : x = e
  all_goals
    simp_all [single_eval]

lemma single_pos {e : E} :
    0 < single e := by
  apply lt_of_le_of_ne single_nonneg (DFunLike.ne_iff.2 _)
  use e
  simp [single_eval]

lemma logCounting_single [ProperSpace E] {e : E} {r : ℝ} (hr : ‖e‖ ≤ r) :
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

lemma logCounting_strictMono [ProperSpace E] {D : locallyFinsuppWithin (univ : Set E) ℤ} {e : E}
    (hD : single e ≤ D) :
    StrictMonoOn (logCounting D) (Ioi ‖e‖) := by
  have : D = (single e) + (D - single e) := by
    abel
  have : logCounting D = logCounting (single e) + logCounting (D - single e) := by
    rw [this]
    have := logCounting.map_add (single e) (D - single e)
    rw [this]
    simp
  rw [this]
  have : logCounting (single e) + logCounting (D - single e) =
    fun r ↦ logCounting (single e) r + logCounting (D - single e) r := rfl
  rw [this]
  apply StrictMonoOn.add_monotone
  · intro a ha b hb hab
    simp at ha hb
    rw [logCounting_single (e := e) ha.le]
    rw [logCounting_single (e := e) hb.le]
    gcongr
    apply (norm_nonneg e).trans_lt ha
  · intro a ha b hb hab
    apply logCounting_mono
    simp [hD]
    simp at ⊢ ha hb
    exact (norm_nonneg e).trans_lt ha
    exact (norm_nonneg e).trans_lt hb
    exact hab

lemma logCounting_single_isBigO_log' [ProperSpace E] {e : E} :
    logCounting (single e) =O[atTop] log := by
  rw [isBigO_iff]
  use 2
  rw [eventually_atTop]
  use max ‖e‖ (exp |log ‖e‖|)
  intro r hr
  have h₁r : ‖e‖ ≤ r := le_of_max_le_left hr
  have h₂r : exp |log ‖e‖| ≤ r := le_of_max_le_right hr
  have h₃r : 1 ≤ r := by
    linarith [h₂r, one_le_exp (abs_nonneg (log ‖e‖))]
  rw [logCounting_single h₁r]
  calc ‖log r - log ‖e‖‖
    _ ≤ ‖log r‖ + ‖log ‖e‖‖ := by
      apply norm_sub_le
    _ ≤ 2 * ‖log r‖ := by
      simpa [two_mul, norm_of_nonneg (log_nonneg h₃r)] using
        (log_le_log (exp_pos _) h₂r)

lemma one_isLittleO_logCounting_single [ProperSpace E] {e : E} :
    (1 : ℝ → ℝ) =o[atTop] logCounting (single e) := by
  rw [isLittleO_iff]
  intro c hc
  simp
  use exp (|log ‖e‖| + c⁻¹)
  intro b hb
  have h₁b : 1 ≤ b := by
    trans rexp (|log ‖e‖| + c⁻¹)
    · apply one_le_exp
      apply add_nonneg
      · exact abs_nonneg (log ‖e‖)
      · exact (inv_pos.2 hc).le
    · exact hb
  rw [← inv_mul_le_iff₀ hc, mul_one]
  rw [abs_of_nonneg (logCounting_nonneg single_nonneg h₁b)]

  trans logCounting (single e) (rexp (|log ‖e‖| + c⁻¹))
  · rw [logCounting_single]
    rw [le_sub_iff_add_le']
    simp [le_abs_self (log ‖e‖)]
    --
    trans rexp (log ‖e‖)
    · by_cases he : ‖e‖ = 0
      · simp [he]
      rw [exp_log]
      aesop
    · apply exp_monotone
      nth_rw 1 [← add_zero (a := log ‖e‖)]
      gcongr
      · exact le_abs_self (log ‖e‖)
      · exact (inv_pos.2 hc).le
  · apply logCounting_mono single_nonneg
    · simp [exp_pos]
    · simp
      apply one_pos.trans_le h₁b
    exact hb

lemma zero_iff_logCounting_bounded [ProperSpace E] {D : locallyFinsuppWithin (univ : Set E) ℤ}
    (h : 0 ≤ D) :
    D = 0 ↔ logCounting D =O[atTop] (1 : ℝ → ℝ) := by
  constructor
  · intro h₂
    simp [isBigO_of_le' (c := 0), h₂]
  · contrapose
    intro h₁
    obtain ⟨e, he⟩ := xx h h₁

    have := one_isLittleO_logCounting_single (e := e)
    rw [isLittleO_iff] at this
    simp at this

    rw [isBigO_iff'']
    push_neg
    intro a ha
    simp
    rw [frequently_atTop]

    intro b

    have := this ha
    obtain ⟨c, hc⟩ := this
    let ℓ := 1 + max ‖e‖ (max |b| |c|)
    have h₁ℓ : b < ℓ := by
      calc b
        _ ≤ |b| := le_abs_self b
        _ ≤ max |b| |c| := le_max_left |b| |c|
        _ ≤ max ‖e‖ (max |b| |c|) := le_max_right ‖e‖ (max |b| |c|)
        _ < 1 + max ‖e‖ (max |b| |c|) := lt_one_add (max ‖e‖ (max |b| |c|))
        _ = ℓ := rfl
    have h₂ℓ : c < ℓ := by
      calc c
        _ ≤ |c| := le_abs_self c
        _ ≤ max |b| |c| := le_max_right |b| |c|
        _ ≤ max ‖e‖ (max |b| |c|) := le_max_right ‖e‖ (max |b| |c|)
        _ < 1 + max ‖e‖ (max |b| |c|) := lt_one_add (max ‖e‖ (max |b| |c|))
        _ = ℓ := rfl
    have h₃ℓ : 1 ≤ ℓ := by
      simp [ℓ]
    have h₄ℓ : ℓ > ‖e‖ := by
      calc ‖e‖
        _ ≤ max ‖e‖ (max |b| |c|) := le_max_left ‖e‖ (max |b| |c|)
        _ < 1 + max ‖e‖ (max |b| |c|) := lt_one_add (max ‖e‖ (max |b| |c|))
        _ = ℓ := rfl
    use 1 + ℓ, h₁ℓ.le.trans (lt_one_add ℓ).le
    calc 1
      _ ≤ (a * |logCounting (single e) ℓ|) := hc ℓ h₂ℓ.le
      _ ≤ (a * |logCounting D ℓ|) := by
        gcongr
        · apply logCounting_nonneg single_nonneg h₃ℓ
        · apply logCounting_le he h₃ℓ
      _ < a * |logCounting D (1 + ℓ)| := by
        gcongr 2
        rw [abs_of_nonneg (logCounting_nonneg h h₃ℓ)]
        rw [abs_of_nonneg (logCounting_nonneg h (le_add_of_nonneg_right (zero_le_one.trans h₃ℓ)))]
        apply logCounting_strictMono he
        simp [h₄ℓ]
        simp
        exact h₄ℓ.trans (lt_one_add ℓ)
        exact lt_one_add ℓ

end Function.locallyFinsuppWithin
