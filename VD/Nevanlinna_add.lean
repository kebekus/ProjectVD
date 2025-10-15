import VD.Nevanlinna_add1

open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

theorem meromorphicOrderAt_add_top
    {f₁ f₂ : 𝕜 → E} {x : 𝕜} (hf₁ : meromorphicOrderAt f₁ x = ⊤) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₂ x := by
  rw [meromorphicOrderAt_congr]
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 hf₁] with z hz
  simp_all

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
    a⁺ x = (a x)⁺ := rfl

lemma negPart_apply (a : locallyFinsuppWithin U Y) (x : X) :
    a⁻ x = (a x)⁻ := rfl

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

theorem neg_min {Y : Type*} [AddCommGroup Y] [LinearOrder Y] [AddLeftMono Y] (a b : Y) :
    (min a b)⁻ = max a⁻ b⁻ := by
  rcases lt_trichotomy a b with h | h | h
  · rw [min_eq_left h.le, max_comm, max_eq_right ((le_iff_posPart_negPart a b).1 h.le).2]
  · simp_all
  · rw [min_comm, min_eq_left h.le, max_eq_right ((le_iff_posPart_negPart b a).1 h.le).2]

namespace ValueDistribution

variable [ProperSpace 𝕜]


theorem min_divisor_le_divisor_add [NormedSpace ℂ E] {f₁ f₂ : ℂ → E} {z : ℂ} {U : Set ℂ} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) (h₁z : z ∈ U) (h₃ : meromorphicOrderAt (f₁ + f₂) z ≠ ⊤) :
    min (divisor f₁ U z) (divisor f₂ U z) ≤ divisor (f₁ + f₂) U z := by
  by_cases hz : z ∉ U
  · simp_all
  simp only [Decidable.not_not] at hz
  rw [divisor_apply hf₁ hz, divisor_apply hf₂ hz, divisor_apply (hf₁.add hf₂) hz]
  by_cases h₁ : meromorphicOrderAt f₁ z = ⊤
  · simp
    right
    rwa [meromorphicOrderAt_add_top]
  by_cases h₂ : meromorphicOrderAt f₂ z = ⊤
  · simp
    left
    rwa [add_comm, meromorphicOrderAt_add_top]
  rw [← WithTop.min_untop₀ h₁ h₂]
  apply WithTop.untop₀_le_untop₀_of_le h₃
  exact meromorphicOrderAt_add (hf₁ z hz) (hf₂ z hz)

theorem negPart_divisor_add_le_max [NormedSpace ℂ E] {f₁ f₂ : ℂ → E} {U : Set ℂ} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ ≤ max (divisor f₁ U)⁻ (divisor f₂ U)⁻ := by
  intro z
  by_cases hz : z ∉ U
  · simp [hz]
  simp at hz
  simp only [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.max_apply]
  by_cases hf₁₂ : meromorphicOrderAt (f₁ + f₂) z = ⊤
  · simp [divisor_apply (hf₁.add hf₂) hz, hf₁₂, negPart_nonneg]
  rw [← neg_min]
  apply ((le_iff_posPart_negPart _ _).1 (min_divisor_le_divisor_add hf₁ hf₂ hz hf₁₂)).2

theorem negPart_divisor_add_le_add [NormedSpace ℂ E] {f₁ f₂ : ℂ → E} {U : Set ℂ} (hf₁ : MeromorphicOn f₁ U) (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ ≤ (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
  calc (divisor (f₁ + f₂) U)⁻
  _ ≤ max (divisor f₁ U)⁻ (divisor f₂ U)⁻ :=
    negPart_divisor_add_le_max hf₁ hf₂
  _ ≤ (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
    by_cases h : (divisor f₁ U)⁻ ≤ (divisor f₂ U)⁻
    · simp_all [negPart_nonneg]
    simp_all [negPart_nonneg]

/--
The counting function of `f + g` at `⊤` is less than or equal to the sum of the
counting functions of `f` and `g`.
-/
theorem counting_top_add_le [NormedSpace ℂ E] {f₁ f₂ : ℂ → E} {r : ℝ}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₁f₂ : MeromorphicOn f₂ Set.univ) (hr : 1 ≤ r) :
    logCounting (f₁ + f₂) ⊤ r ≤ ((logCounting f₁ ⊤) + (logCounting f₂ ⊤)) r := by
  simp only [logCounting, ↓reduceDIte]
  rw [← Function.locallyFinsuppWithin.logCounting.map_add]
  exact Function.locallyFinsuppWithin.logCounting_le (negPart_divisor_add_le_add h₁f₁ h₁f₂) hr

theorem counting_top_sum_le [NormedSpace ℂ E] {α : Type*} (s : Finset α) (f : α → ℂ → E)
    {r : ℝ} (h₁f : ∀ a, MeromorphicOn (f a) Set.univ) (hr : 1 ≤ r) :
    logCounting (∑ a ∈ s, f a) ⊤ r ≤ (∑ a ∈ s, (logCounting (f a) ⊤)) r := by
  induction s using Finset.induction with
  | empty =>
    simp_all
    sorry
  | insert a s ha hs =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc logCounting (f a + ∑ x ∈ s, f x) ⊤ r
    _ ≤ (logCounting (f a) ⊤ + logCounting (∑ x ∈ s, f x) ⊤) r :=
      counting_top_add_le (h₁f a) (MeromorphicOn.sum h₁f) hr
    _ ≤ (logCounting (f a) ⊤ + ∑ x ∈ s, logCounting (f x) ⊤) r :=
      add_le_add (by trivial) hs


end ValueDistribution
