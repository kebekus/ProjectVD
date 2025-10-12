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

theorem logCounting_nonneg {f : locallyFinsuppWithin (univ : Set E) ℤ} {r : ℝ} (h : 0 ≤ f) (hr : 1 ≤ r) :
    0 ≤ logCounting f r := by
  have h₃r : 0 < r := by linarith
  apply add_nonneg
  · apply finsum_nonneg
    · intro a
      by_cases h₁a : a = 0
      · simp_all
      by_cases h₂a : a ∈ closedBall 0 |r|
      · apply mul_nonneg
        · simpa [toClosedBall, restrictMonoidHom_apply, restrict_apply, h₂a] using h a
        · rw [log_nonneg_iff]
          · rw [← inv_le_iff_one_le_mul₀]
            · rw [inv_inv, ← abs_of_pos h₃r]
              simp_all
            · rwa [inv_pos, norm_pos_iff]
          · simp_all
      · simp [apply_eq_zero_of_notMem ((toClosedBall r) _) h₂a]
  · apply mul_nonneg (by simpa using h 0) (log_nonneg hr)

theorem logCounting_le {f₁ f₂ : locallyFinsuppWithin (univ : Set E) ℤ} {r : ℝ} (h : f₁ ≤ f₂) (hr : 1 ≤ r) :
    logCounting f₁ r ≤ logCounting f₂ r := by
  rw [← sub_nonneg] at h ⊢
  simpa using logCounting_nonneg h hr

theorem logCounting_eventually_le {f₁ f₂ : locallyFinsuppWithin (univ : Set E) ℤ} (h : f₁ ≤ f₂) :
    logCounting f₁ ≤ᶠ[Filter.atTop] logCounting f₂ := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ logCounting_le h hr

end Function.locallyFinsuppWithin

namespace ValueDistribution

variable [ProperSpace 𝕜]

/--
For `1 ≤ r`, the counting function counting zeros of `f * g` is less than or
equal to the sum of the counting functions counting zeros of `f` and `g`,
respectively.
-/
theorem logCounting_zero_mul_le {f₁ f₂ : 𝕜 → 𝕜} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z ∈ univ, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z ∈ univ, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) 0 r ≤ (logCounting f₁ 0 + logCounting f₂ 0) r := by
  simp only [logCounting, WithTop.zero_ne_top, reduceDIte, WithTop.untop₀_zero, sub_zero]
  rw [divisor_mul h₁f₁ h₁f₂ h₂f₁ h₂f₂, ← Function.locallyFinsuppWithin.logCounting.map_add]
  apply Function.locallyFinsuppWithin.logCounting_le _ hr
  apply Function.locallyFinsuppWithin.posPart_add

/--
Asymptotically, the counting function counting poles of `f * g` is less than or
equal to the sum of the counting functions counting poles of `f` and `g`,
respectively.
-/
theorem logCounting_top_mul_le {f₁ f₂ : 𝕜 → 𝕜} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z ∈ univ, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z ∈ univ, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) ⊤ r ≤ (logCounting f₁ ⊤ + logCounting f₂ ⊤) r := by
  simp only [logCounting, reduceDIte]
  rw [divisor_mul h₁f₁ h₁f₂ h₂f₁ h₂f₂, ← Function.locallyFinsuppWithin.logCounting.map_add]
  apply Function.locallyFinsuppWithin.logCounting_le _ hr
  apply Function.locallyFinsuppWithin.negPart_add

/--
For `1 ≤ r`, the counting function counting zeros of `f * g` is less than or
equal to the sum of the counting functions counting zeros of `f` and `g`,
respectively.
-/
theorem logCounting_zero_mul_eventually_le {f₁ f₂ : 𝕜 → 𝕜}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z ∈ univ, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z ∈ univ, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) 0 ≤ᶠ[Filter.atTop] logCounting f₁ 0 + logCounting f₂ 0 := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ logCounting_zero_mul_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
Asymptotically, the counting function counting zeros of `f * g` is less than or
equal to the sum of the counting functions counting zeros of `f` and `g`,
respectively.
-/
theorem logCounting_top_mul_eventually_le {f₁ f₂ : 𝕜 → 𝕜}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z ∈ univ, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z ∈ univ, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) ⊤ ≤ᶠ[Filter.atTop] logCounting f₁ ⊤ + logCounting f₂ ⊤ := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ logCounting_top_mul_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

end ValueDistribution
