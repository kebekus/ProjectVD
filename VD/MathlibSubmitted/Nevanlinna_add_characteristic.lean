import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction

open MeromorphicOn Real

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

namespace ValueDistribution

variable [ProperSpace 𝕜]

/--
For `1 ≤ r`, the characteristic function of `f + g` at `⊤` is less than or equal to
the sum of the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_add_top_le [NormedSpace ℂ E] {f₁ f₂ : ℂ → E} {r : ℝ}
    (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) (hr : 1 ≤ r) :
    characteristic (f₁ + f₂) ⊤ r ≤ characteristic f₁ ⊤ r + characteristic f₂ ⊤ r + log 2 := by
  simp [characteristic]
  calc proximity (f₁ + f₂) ⊤ r + logCounting (f₁ + f₂) ⊤ r
  _ ≤ (proximity f₁ ⊤ r + proximity f₂ ⊤ r + log 2) + (logCounting f₁ ⊤ r + logCounting f₂ ⊤ r) := by
    apply add_le_add
    · apply proximity_add_top_le h₁f₁ h₁f₂
    · exact logCounting_add_top_le h₁f₁ h₁f₂ hr
  _ = proximity f₁ ⊤ r + logCounting f₁ ⊤ r + (proximity f₂ ⊤ r + logCounting f₂ ⊤ r) + log 2 := by
    ring

/--
Asymptotically, the characteristic function of `f + g` at `⊤` is less than or equal to
the sum of the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_add_top_eventuallyLE [NormedSpace ℂ E] {f₁ f₂ : ℂ → E}
    (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) :
    characteristic (f₁ + f₂) ⊤ ≤ᶠ[Filter.atTop] characteristic f₁ ⊤ + characteristic f₂ ⊤ + fun _ ↦ log 2 := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ characteristic_add_top_le h₁f₁ h₁f₂ hr

/--
For `1 ≤ r`, the characteristic function of a sum `∑ a, f a` at `⊤` is less than or
equal to the sum of the characteristic functions of `f ·`.
-/
theorem characteristic_sum_top_le [NormedSpace ℂ E] {α : Type*} (s : Finset α) (f : α → ℂ → E)
    {r : ℝ} (hf : ∀ a, Meromorphic (f a)) (hr : 1 ≤ r) :
    characteristic (∑ a ∈ s, f a) ⊤ r ≤ (∑ a ∈ s, (characteristic (f a) ⊤)) r + log s.card := by
  simp [characteristic]
  calc proximity (∑ a ∈ s, f a) ⊤ r + logCounting (∑ a ∈ s, f a) ⊤ r
  _ ≤ ((∑ a ∈ s, proximity (f a) ⊤) r) + log s.card + (∑ a ∈ s, (logCounting (f a) ⊤)) r := by
    apply add_le_add
    · apply proximity_sum_top_le s f hf r
    · apply logCounting_sum_top_le s f hf hr
  _ = ((∑ a ∈ s, proximity (f a) ⊤) r) + (∑ a ∈ s, (logCounting (f a) ⊤)) r + log s.card := by
    ring
  _ = ∑ x ∈ s, (proximity (f x) ⊤ r + logCounting (f x) ⊤ r) + log s.card := by
    simp [Finset.sum_add_distrib]

/--
Asymptotically, the characteristic function of a sum `∑ a, f a` at `⊤` is less than or
equal to the sum of the characteristic functions of `f ·`.
-/
theorem characteristic_sum_top_eventuallyLE [NormedSpace ℂ E] {α : Type*} (s : Finset α) (f : α → ℂ → E)
    (hf : ∀ a, Meromorphic (f a)) :
    characteristic (∑ a ∈ s, f a) ⊤
      ≤ᶠ[Filter.atTop] ∑ a ∈ s, (characteristic (f a) ⊤) + fun _ ↦ log s.card := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ characteristic_sum_top_le s f hf hr

end ValueDistribution
