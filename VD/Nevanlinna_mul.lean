import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Analysis.Complex.ValueDistribution.CountingFunction

open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

theorem finsum_le_finsum
    {α R : Type*} [AddCommMonoid R] [LinearOrder R] [AddLeftMono R]
    (f₁ f₂ : α → R) (hf : f₁ ≤ f₂) (hf₁ : f₁.support.Finite) (hf₂ : f₂.support.Finite) :
    ∑ᶠ (a : α), f₁ a ≤ ∑ᶠ (a : α), f₂ a := by
  rw [finsum_eq_sum_of_support_subset f₁ (by simp : f₁.support ⊆ (hf₁.toFinset ∪ hf₂.toFinset : Finset α))]
  rw [finsum_eq_sum_of_support_subset f₂ (by simp : f₂.support ⊆ (hf₁.toFinset ∪ hf₂.toFinset : Finset α))]
  exact Finset.sum_le_sum fun a _ ↦ hf a

/-!
Statements about functions with locally finite support
-/

namespace Function.locallyFinsuppWithin

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*} [AddCommGroup Y] [LinearOrder Y]

instance x [IsOrderedAddMonoid Y] : IsOrderedAddMonoid (locallyFinsuppWithin U Y) where
  add_le_add_left _ _ h _ x := by simp [h x]

theorem posPart_le
    {f₁ f₂ : Function.locallyFinsuppWithin U Y} (h : f₁ ≤ f₂):
    f₁⁺ ≤ f₂⁺ := by
  intro x
  by_cases hf : f₁ x ≤ 0
  · simp [instPosPart, hf]
  · simp [instPosPart, h x, (lt_of_lt_of_le (not_le.1 hf) (h x)).le]

theorem negPart_le [IsOrderedAddMonoid Y]
    {f₁ f₂ : Function.locallyFinsuppWithin U Y} (h : f₁ ≤ f₂):
    f₂⁻ ≤ f₁⁻ := by
  intro x
  by_cases hf : -f₁ x ≤ 0
  · simp_all only [Left.neg_nonpos_iff, instNegPart, max_apply, coe_neg, Pi.neg_apply, coe_zero,
      Pi.zero_apply, sup_of_le_right, sup_le_iff, le_refl, and_true]
    exact Std.IsPreorder.le_trans 0 (f₁ x) (f₂ x) hf (h x)
  · rw [Left.neg_nonpos_iff, not_le] at hf
    simp_all [instNegPart, h x, hf.le]

variable [IsOrderedAddMonoid Y]

theorem posPart_add
    (f₁ f₂ : Function.locallyFinsuppWithin U Y) :
    (f₁ + f₂)⁺ ≤ f₁⁺ + f₂⁺ := by
  rw [instPosPart, Function.locallyFinsuppWithin.le_def]
  intro x
  simp only [Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.coe_add,
    Pi.add_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor
  · simp [add_le_add]
  · simp [add_nonneg]

theorem negPart_add
    (f₁ f₂ : Function.locallyFinsuppWithin U Y) :
    (f₁ + f₂)⁻ ≤ f₁⁻ + f₂⁻ := by
  rw [instNegPart, Function.locallyFinsuppWithin.le_def]
  intro x
  simp only [neg_add_rev, Function.locallyFinsuppWithin.max_apply,
    Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_neg, Pi.add_apply,
    Pi.neg_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor
  · simp [add_comm, add_le_add]
  · simp [add_nonneg]

theorem evenlogCounting (f : locallyFinsuppWithin (univ : Set E) ℤ) :
    (logCounting f).Even := by
  intro r
  simp [logCounting, toClosedBall]
  rw [abs_neg r]

theorem logCounting_le {f₁ f₂ : locallyFinsuppWithin (univ : Set E) ℤ} {r : ℝ} (h : f₁ ≤ f₂) (hr : 0 ≤ r) :
    logCounting f₁⁺ r ≤ logCounting f₂⁺ r := by
  by_cases h₂r : r = 0
  · rw [h₂r, logCounting_eval_zero, logCounting_eval_zero]
  simp [logCounting]
  apply add_le_add
  · apply finsum_le_finsum
    · intro a
      by_cases h₁a : a = 0
      · simp_all
      by_cases h₂a : a ∈ closedBall 0 |r|
      · apply mul_le_mul
        · simp [toClosedBall, restrictMonoidHom_apply, restrict_apply, h₂a, posPart_le h a]
        · rfl
        · rw [log_nonneg_iff]
          · rw [← inv_le_iff_one_le_mul₀]
            · rw [inv_inv]
              rw [← abs_of_nonneg hr]
              simp_all
            · rw [inv_pos, norm_pos_iff]
              exact h₁a
          · simp_all [lt_of_le_of_ne hr (fun a ↦ h₂r (a.symm))]
        · simp [toClosedBall, restrictMonoidHom_apply, restrict_apply, h₂a]
          apply posPart_nonneg
      · simp [apply_eq_zero_of_notMem ((toClosedBall r) _) h₂a]
    · rw [support_mul]
      apply Finite.inter_of_left
      rw [(by aesop : (fun a ↦ (((toClosedBall r) f₁⁺) a) : E → ℝ).support = (toClosedBall r f₁⁺).support)]
      apply finiteSupport _ (isCompact_closedBall 0 |r|)
    · rw [support_mul]
      apply Finite.inter_of_left
      rw [(by aesop : (fun a ↦ (((toClosedBall r) f₂⁺) a) : E → ℝ).support = (toClosedBall r f₂⁺).support)]
      apply finiteSupport _ (isCompact_closedBall 0 |r|)
  · apply mul_le_mul
    · simpa using posPart_le h 0
    · rfl
    · exact (log_pos hr).le
    · simpa using posPart_nonneg f₂ 0

end Function.locallyFinsuppWithin

namespace ValueDistribution

variable [ProperSpace 𝕜]

/--
The counting function counting zeros of `f * g` is less than or equal to the sum
of the counting functions counting zeros of `f` and `g`, respectively.
-/
@[simp] theorem logCounting_mul {f₁ f₂ : 𝕜 → 𝕜} (hf₁ : MeromorphicOn f₁ Set.univ) (hf₂ : MeromorphicOn f₂ Set.univ) :
    logCounting (f₁ * f₂) 0 ≤ logCounting f₁ 0 + logCounting f₂ 0 := by
  unfold logCounting
  simp only [WithTop.zero_ne_top, ↓reduceDIte, WithTop.untop₀_zero, sub_zero]
  rw [divisor_mul hf₁ hf₂]
  rw [← Function.locallyFinsuppWithin.logCounting.map_add]
  simp
  sorry

end ValueDistribution
