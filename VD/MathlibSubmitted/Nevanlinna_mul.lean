import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Analysis.Complex.ValueDistribution.CountingFunction
import Mathlib.Analysis.Complex.ValueDistribution.ProximityFunction

open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

/--
Circle averages respect the `≤` relation.
-/
theorem circleAverage_mono {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℝ} (hf₁ : CircleIntegrable f₁ c R)
    (hf₂ : CircleIntegrable f₂ c R) (h : ∀ x ∈ Metric.sphere c |R|, f₁ x ≤ f₂ x) :
    circleAverage f₁ c R ≤ circleAverage f₂ c R := by
  apply (mul_le_mul_iff_of_pos_left (by simp [pi_pos])).2
  apply intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos) hf₁ hf₂
  exact fun x _ ↦ by simp [h (circleMap c R x)]


namespace Function.locallyFinsuppWithin

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*} [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]

/--
The positive part of a sum is less than or equal to the sum of the positive parts.
-/
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

/--
The negative part of a sum is less than or equal to the sum of the negative parts.
-/
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

/--
For `1 ≤ r`, the counting function is non-negative.
-/
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

/--
For `1 ≤ r`, the counting function respects the `≤` relation.
-/
theorem logCounting_le {f₁ f₂ : locallyFinsuppWithin (univ : Set E) ℤ} {r : ℝ} (h : f₁ ≤ f₂) (hr : 1 ≤ r) :
    logCounting f₁ r ≤ logCounting f₂ r := by
  rw [← sub_nonneg] at h ⊢
  simpa using logCounting_nonneg h hr

/--
The counting function respects the `≤` relation asymptotically.
-/
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
Asymptotically, the counting function counting zeros of `f * g` is less than or
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
For `1 ≤ r`, the counting function counting poles of `f * g` is less than or
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

/--
The proximity function `f * g` at `⊤` is less than or equal to the sum of the
proximity functions of `f` and `g`, respectively.
-/
theorem proximity_top_mul_le {f₁ f₂ : ℂ → ℂ} (h₁f₁ : MeromorphicOn f₁ Set.univ)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) :
    proximity (f₁ * f₂) ⊤ ≤ (proximity f₁ ⊤) + (proximity f₂ ⊤) := by
  calc proximity (f₁ * f₂) ⊤
  _ = circleAverage (fun x ↦ log⁺ (‖f₁ x‖ * ‖f₂ x‖)) 0 := by
    simp [proximity]
  _ ≤ circleAverage (fun x ↦ log⁺ ‖f₁ x‖ + log⁺ ‖f₂ x‖) 0 := by
    intro r
    apply circleAverage_mono
    · simp_rw [← norm_mul]
      apply circleIntegrable_posLog_norm_meromorphicOn
      exact fun_mul (fun x a ↦ h₁f₁ x trivial) fun x a ↦ h₁f₂ x trivial
    · apply (circleIntegrable_posLog_norm_meromorphicOn (fun x a ↦ h₁f₁ x trivial)).add
        (circleIntegrable_posLog_norm_meromorphicOn (fun x a ↦ h₁f₂ x trivial))
    · exact fun _ _ ↦ posLog_mul
  _ = circleAverage (log⁺ ‖f₁ ·‖) 0 + circleAverage (log⁺ ‖f₂ ·‖) 0:= by
    ext r
    apply circleAverage_add
    · exact circleIntegrable_posLog_norm_meromorphicOn (fun x a ↦ h₁f₁ x trivial)
    · exact circleIntegrable_posLog_norm_meromorphicOn (fun x a ↦ h₁f₂ x trivial)
  _ = (proximity f₁ ⊤) + (proximity f₂ ⊤) := rfl

/--
The proximity function `f * g` at `0` is less than or equal to the sum of the
proximity functions of `f` and `g`, respectively.
-/
theorem proximity_zero_mul_le {f₁ f₂ : ℂ → ℂ} (h₁f₁ : MeromorphicOn f₁ Set.univ)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) :
    proximity (f₁ * f₂) 0 ≤ (proximity f₁ 0) + (proximity f₂ 0) := by
  calc proximity (f₁ * f₂) 0
  _ ≤ (proximity f₁⁻¹ ⊤) + (proximity f₂⁻¹ ⊤) := by
    rw [← proximity_inv, mul_inv]
    apply proximity_top_mul_le (inv_iff.mpr h₁f₁) (inv_iff.mpr h₁f₂)
  _ = (proximity f₁ 0) + (proximity f₂ 0) := by
    rw [proximity_inv, proximity_inv]

/--
For `1 ≤ r`, the characteristic function of `f * g` at zero is less than or
equal to the sum of the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_zero_mul_le {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z ∈ univ, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z ∈ univ, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) 0 r ≤ (characteristic f₁ 0 + characteristic f₂ 0) r := by
  simp only [characteristic, Pi.add_apply]
  have {A B C D : ℝ} : A + B + (C + D) = (A + C) + (B + D) := by ring
  rw [this]
  apply add_le_add (proximity_zero_mul_le h₁f₁ h₁f₂ r)
    (logCounting_zero_mul_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

/--
Asymptotically, the characteristic function of `f * g` at zero is less than or
equal to the sum of the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_zero_mul_eventually_le {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z ∈ univ, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z ∈ univ, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) 0 ≤ᶠ[Filter.atTop] characteristic f₁ 0 + characteristic f₂ 0 := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ characteristic_zero_mul_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For `1 ≤ r`, the characteristic function of `f * g` at `⊤` is less than or equal
to the sum of the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_top_mul_le {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z ∈ univ, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z ∈ univ, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) ⊤ r ≤ (characteristic f₁ ⊤ + characteristic f₂ ⊤) r := by
  simp only [characteristic, Pi.add_apply]
  have {A B C D : ℝ} : A + B + (C + D) = (A + C) + (B + D) := by ring
  rw [this]
  apply add_le_add (proximity_top_mul_le h₁f₁ h₁f₂ r)
    (logCounting_top_mul_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

/--
Asymptotically, the characteristic function of `f * g` at `⊤` is less than or
equal to the sum of the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_top_mul_eventually_le {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z ∈ univ, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z ∈ univ, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) ⊤ ≤ᶠ[Filter.atTop] characteristic f₁ ⊤ + characteristic f₂ ⊤ := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ characteristic_top_mul_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

end ValueDistribution
