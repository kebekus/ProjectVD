import VD.ToMathlib.Nevanlinna_mul

open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}


@[simp]
theorem WithTop.max_untop₀ {α : Type*} [AddCommGroup α] [LinearOrder α] {a b : WithTop α}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (max a b).untop₀ = max a.untop₀ b.untop₀ := by
  lift a to α using ha
  lift b to α using hb
  simp only [untop₀_coe]
  by_cases h : a ≤ b
  · simp [max_eq_right h, max_eq_right (coe_le_coe.mpr h)]
  rw [not_le] at h
  simp [max_eq_left h.le, max_eq_left (coe_lt_coe.mpr h).le]

@[simp]
theorem WithTop.min_untop₀ {α : Type*} [AddCommGroup α] [LinearOrder α] {a b : WithTop α}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (min a b).untop₀ = min a.untop₀ b.untop₀ := by
  lift a to α using ha
  lift b to α using hb
  simp only [untop₀_coe]
  by_cases h : a ≤ b
  · simp [min_eq_left h, min_eq_left (coe_le_coe.mpr h)]
  rw [not_le] at h
  simp [min_eq_right h.le, min_eq_right (coe_lt_coe.mpr h).le]

@[simp]
theorem WithTop.le_of_untop₀_le_untop₀ {α : Type*} [AddCommGroup α] [LinearOrder α] {a b : WithTop α}
    (ha : a ≠ ⊤) (h : a.untop₀ ≤ b.untop₀) :
    a ≤ b := by
  lift a to α using ha
  by_cases hb : b = ⊤
  · simp_all
  lift b to α using hb
  simp_all

@[simp]
theorem WithTop.untop₀_le_untop₀_of_le {α : Type*} [AddCommGroup α] [LinearOrder α] {a b : WithTop α}
    (hb : b ≠ ⊤) (h : a ≤ b) :
    a.untop₀ ≤ b.untop₀ := by
  lift b to α using hb
  by_cases ha : a = ⊤
  · simp_all
  lift a to α using ha
  simp_all

namespace Function.locallyFinsuppWithin

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*} [AddCommGroup Y] [LinearOrder Y]

lemma posPart_apply (a : locallyFinsuppWithin U Y) (x : X) :
    a⁺ x = (a x)⁺ := by rfl

lemma negPart_apply (a : locallyFinsuppWithin U Y) (x : X) :
    a⁻ x = (a x)⁻ := by rfl

variable [IsOrderedAddMonoid Y]

theorem neg_min (a b : locallyFinsuppWithin U Y) :
    (min a b)⁻ = max a⁻ b⁻ := by
  ext x
  rw [max_apply, negPart_apply, negPart_apply, negPart_apply, min_apply]
  rcases lt_trichotomy (a x) (b x) with h | h | h
  · rw [min_eq_left h.le, max_comm, max_eq_right ((le_iff_posPart_negPart (a x) (b x)).1 h.le).2]
  · simp_all
  · rw [min_comm, min_eq_left h.le, max_eq_right ((le_iff_posPart_negPart (b x) (a x)).1 h.le).2]

end Function.locallyFinsuppWithin

namespace ValueDistribution

variable [ProperSpace 𝕜]


theorem xx₁ {f₁ f₂ : ℂ → ℂ} {z : ℂ} {U : Set ℂ} (hf₁ : MeromorphicOn f₁ U)  (hf₂ : MeromorphicOn f₂ U)
    (h₁z : z ∈ U) (h₃ : meromorphicOrderAt (f₁ + f₂) z ≠ ⊤) :
    min (divisor f₁ U z) (divisor f₂ U z) ≤ divisor (f₁ + f₂) U z := by
  by_cases hz : z ∉ U
  · simp_all
  simp only [Decidable.not_not] at hz
  rw [divisor_apply hf₁ hz, divisor_apply hf₂ hz, divisor_apply (hf₁.add hf₂) hz]
  by_cases h₁ : meromorphicOrderAt f₁ z = ⊤
  · sorry
  have h₂ : meromorphicOrderAt f₂ z ≠ ⊤ := by sorry
  rw [← WithTop.min_untop₀ h₁ h₂]
  apply WithTop.untop₀_le_untop₀_of_le (h₃ z hz)
  exact meromorphicOrderAt_add (hf₁ z hz) (hf₂ z hz)


theorem xx₂ {f₁ f₂ : ℂ → ℂ} {U : Set ℂ} (hf₁ : MeromorphicOn f₁ U)  (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ ≤ (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
  intro z
  by_cases hz : z ∉ U
  · simp [hz]
  simp at hz
  simp [Function.locallyFinsuppWithin.negPart_apply]
  by_cases hf₁₂ : meromorphicOrderAt (f₁ + f₂) z = ⊤
  · sorry

  have := xx₁ hf₁ hf₂ hz hf₁₂

  have A := ((le_iff_posPart_negPart (min (divisor f₁ U z) (divisor f₂ U z)) (divisor (f₁ + f₂) U z)).1 this).2
  rw [Function.locallyFinsuppWithin.neg_min] at A
  intro z

  intro z
  simp
  rw [negPart]
  --rw [instNegPart]
  simp [instNegPart]
  rw [Function.locallyFinsuppWithin.min_apply]

  rw [Function.locallyFinsuppWithin.instNegPart]
  sorry

/--
The counting function of `f + g` at `⊤` is less than or equal to the sum of the
counting functions of `f` and `g`.
-/
theorem counting_top_add_le {f₁ f₂ : ℂ → ℂ} (h₁f₁ : MeromorphicOn f₁ Set.univ)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) :
    logCounting (f₁ + f₂) ⊤ ≤ (logCounting f₁ ⊤) + (logCounting f₂ ⊤) := by
  simp [logCounting]
  sorry

end ValueDistribution
