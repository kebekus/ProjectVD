import VD.MathlibSubmitted.DivisorOrder
import VD.MathlibSubmitted.MeromorphicSum
import VD.MathlibSubmitted.Nevanlinna_mul

open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

-- DUPLICATE!
theorem meromorphicOrderAt_const (z₀ : 𝕜) (e : E) :
    meromorphicOrderAt (fun _ ↦ e) z₀ = if e = 0 then ⊤ else (0 : WithTop ℤ) := by
  by_cases he : e = 0
  · simp [he, meromorphicOrderAt_eq_top_iff]
  simp [he]
  rw [(by rfl : (0 : WithTop ℤ) = (0 : ℤ)), meromorphicOrderAt_eq_int_iff (MeromorphicAt.const e z₀)]
  use fun _ ↦ e
  simp [he]
  fun_prop

-- DUPLICATE!
@[simp]
theorem divisor_const (e : E) :
    divisor (fun _ ↦ e) U = 0 := by
  classical
  ext x
  simp only [divisor_def, meromorphicOrderAt_const, Function.locallyFinsuppWithin.coe_zero,
    Pi.zero_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero,
    LinearOrderedAddCommGroupWithTop.top_ne_zero, imp_false, ite_eq_left_iff, WithTop.zero_ne_top,
    Decidable.not_not, and_imp]
  tauto

-- DUPLICATE!
@[simp]
theorem divisor_intCast (n : ℤ) :
    divisor (n : 𝕜 → 𝕜) U = 0 := divisor_const (n : 𝕜)

-- DUPLICATE!
@[simp]
theorem divisor_natCast (n : ℕ) :
    divisor (n : 𝕜 → 𝕜) U = 0 := divisor_const (n : 𝕜)

-- DUPLICATE!
@[simp] theorem divisor_ofNat (n : ℕ) :
    divisor (ofNat(n) : 𝕜 → 𝕜) U = 0 := by
  convert divisor_const (n : 𝕜)
  simp [Semiring.toGrindSemiring_ofNat 𝕜 n]

/--
Adding a locally vanishing function does not change the order.
-/
theorem meromorphicOrderAt_add_top
    {f₁ f₂ : 𝕜 → E} {x : 𝕜} (hf₁ : meromorphicOrderAt f₁ x = ⊤) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₂ x := by
  rw [meromorphicOrderAt_congr]
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 hf₁] with z hz
  simp_all

namespace ValueDistribution

variable [ProperSpace 𝕜]

/--
The counting function of a constant function is zero.
-/
@[simp] theorem logCounting_const
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {c : E} {e : WithTop E} :
    logCounting (fun _ ↦ c : 𝕜 → E) e = 0 := by
  simp [logCounting]

/--
The counting function of the constant function zero is zero.
-/
@[simp] theorem logCounting_const_zero {e : WithTop E} :
    logCounting (0 : 𝕜 → E) e = 0 := logCounting_const

/--
The divisor of `f₁ + f₂` is larger than or equal to the minimum of the divisors
of `f₁` and `f₂`, respectively.
-/
theorem min_divisor_le_divisor_add [NormedSpace ℂ E] {f₁ f₂ : ℂ → E} {z : ℂ} {U : Set ℂ} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) (h₁z : z ∈ U) (h₃ : meromorphicOrderAt (f₁ + f₂) z ≠ ⊤) :
    min (divisor f₁ U z) (divisor f₂ U z) ≤ divisor (f₁ + f₂) U z := by
  by_cases hz : z ∉ U
  · simp_all
  simp only [Decidable.not_not] at hz
  rw [divisor_apply hf₁ hz, divisor_apply hf₂ hz, divisor_apply (hf₁.add hf₂) hz]
  by_cases h₁ : meromorphicOrderAt f₁ z = ⊤
  · rw [inf_le_iff]
    right
    rwa [meromorphicOrderAt_add_top]
  by_cases h₂ : meromorphicOrderAt f₂ z = ⊤
  · rw [inf_le_iff]
    left
    rwa [add_comm, meromorphicOrderAt_add_top]
  rw [← WithTop.untop₀_min h₁ h₂]
  apply WithTop.untop₀_le_untop₀_of_le h₃
  exact meromorphicOrderAt_add (hf₁ z hz) (hf₂ z hz)

/--
The pole divisor of `f₁ + f₂` is smaller than or equal to the maximum of the
pole divisors of `f₁` and `f₂`, respectively.
-/
theorem negPart_divisor_add_le_max [NormedSpace ℂ E] {f₁ f₂ : ℂ → E} {U : Set ℂ} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ ≤ max (divisor f₁ U)⁻ (divisor f₂ U)⁻ := by
  intro z
  by_cases hz : z ∉ U
  · simp [hz]
  rw [Decidable.not_not] at hz
  simp only [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.max_apply]
  by_cases hf₁₂ : meromorphicOrderAt (f₁ + f₂) z = ⊤
  · simp [divisor_apply (hf₁.add hf₂) hz, hf₁₂, negPart_nonneg]
  rw [← negPart_min]
  apply ((le_iff_posPart_negPart _ _).1 (min_divisor_le_divisor_add hf₁ hf₂ hz hf₁₂)).2

/--
The pole divisor of `f₁ + f₂` is smaller than or equal to the sum of the pole
divisors of `f₁` and `f₂`, respectively.
-/
theorem negPart_divisor_add_le_add [NormedSpace ℂ E] {f₁ f₂ : ℂ → E} {U : Set ℂ} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ ≤ (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
  calc (divisor (f₁ + f₂) U)⁻
  _ ≤ max (divisor f₁ U)⁻ (divisor f₂ U)⁻ :=
    negPart_divisor_add_le_max hf₁ hf₂
  _ ≤ (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
    by_cases h : (divisor f₁ U)⁻ ≤ (divisor f₂ U)⁻
    <;> simp_all [negPart_nonneg]

/--
For `1 ≤ r`, the counting function of `f + g` at `⊤` is less than or equal to
the sum of the counting functions of `f` and `g`, respectively.
-/
theorem counting_top_add_le [NormedSpace ℂ E] {f₁ f₂ : ℂ → E} {r : ℝ}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₁f₂ : MeromorphicOn f₂ Set.univ) (hr : 1 ≤ r) :
    logCounting (f₁ + f₂) ⊤ r ≤ ((logCounting f₁ ⊤) + (logCounting f₂ ⊤)) r := by
  simp only [logCounting, ↓reduceDIte]
  rw [← Function.locallyFinsuppWithin.logCounting.map_add]
  exact Function.locallyFinsuppWithin.logCounting_le (negPart_divisor_add_le_add h₁f₁ h₁f₂) hr

/--
Asymptotically, the counting function of `f + g` at `⊤` is less than or equal to
the sum of the counting functions of `f` and `g`, respectively.
-/
theorem counting_top_add_eventually_le [NormedSpace ℂ E] {f₁ f₂ : ℂ → E}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₁f₂ : MeromorphicOn f₂ Set.univ) :
    logCounting (f₁ + f₂) ⊤ ≤ᶠ[Filter.atTop] (logCounting f₁ ⊤) + (logCounting f₂ ⊤) := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ counting_top_add_le h₁f₁ h₁f₂ hr

/--
For `1 ≤ r`, the counting function of a sum `∑ a, f a` at `⊤` is less than or
equal to the sum of the counting functions of `f ·`.
-/
theorem counting_top_sum_le [NormedSpace ℂ E] {α : Type*} (s : Finset α) (f : α → ℂ → E)
    {r : ℝ} (h₁f : ∀ a, MeromorphicOn (f a) Set.univ) (hr : 1 ≤ r) :
    logCounting (∑ a ∈ s, f a) ⊤ r ≤ (∑ a ∈ s, (logCounting (f a) ⊤)) r := by
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha hs =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc logCounting (f a + ∑ x ∈ s, f x) ⊤ r
    _ ≤ (logCounting (f a) ⊤ + logCounting (∑ x ∈ s, f x) ⊤) r :=
      counting_top_add_le (h₁f a) (MeromorphicOn.sum h₁f) hr
    _ ≤ (logCounting (f a) ⊤ + ∑ x ∈ s, logCounting (f x) ⊤) r :=
      add_le_add (by trivial) hs

/--
Asymptotically, the counting function of a sum `∑ a, f a` at `⊤` is less than or
equal to the sum of the counting functions of `f ·`.
-/
theorem counting_top_sum_eventually_le [NormedSpace ℂ E] {α : Type*} (s : Finset α) (f : α → ℂ → E)
    (h₁f : ∀ a, MeromorphicOn (f a) Set.univ) :
    logCounting (∑ a ∈ s, f a) ⊤ ≤ᶠ[Filter.atTop] ∑ a ∈ s, (logCounting (f a) ⊤) := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ counting_top_sum_le s f h₁f hr

end ValueDistribution
