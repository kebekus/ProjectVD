import Mathlib.Analysis.Meromorphic.Order
import VD.ToMathlib.MeromorphicAt_order

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {x : 𝕜}

open Filter Topology

noncomputable def leadCoefficient (f : 𝕜 → E) (x : 𝕜) : E := by
  by_cases h₁ : ¬MeromorphicAt f x
  · exact 0
  rw [not_not] at h₁
  by_cases h₂ : h₁.order = ⊤
  · exact 0
  exact (h₁.order_ne_top_iff.1 h₂).choose x

/-- If `f` is not meromorphic at `x`, the leading coefficient is zero by definition. -/
lemma leadCoefficient_not_MeromorphicAt (h : ¬MeromorphicAt f x) :
    leadCoefficient f x = 0 := by simp_all [leadCoefficient]

/--
If `f` is meromorphic of infinite order at `x`, the leading coefficient is zero
by definition.
-/
lemma leadCoefficient_order_eq_top (h₁ : MeromorphicAt f x) (h₂ : h₁.order = ⊤) :
    leadCoefficient f x = 0 := by simp_all [leadCoefficient]

lemma leadCoefficient_def₀ {g : 𝕜 → E}
    (h₁ : AnalyticAt 𝕜 g x)
    (h₂ : MeromorphicAt f x)
    (h₅ : h₂.order ≠ ⊤)
    (h₃ : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ h₂.order.untop₀ • g z) :
    leadCoefficient f x = g x := by
  unfold leadCoefficient
  simp only [h₂, not_true_eq_false, ↓reduceDIte, h₅, ne_eq]
  obtain ⟨h'₁, h'₂, h'₃⟩ := (h₂.order_ne_top_iff.1 h₅).choose_spec
  apply Filter.EventuallyEq.eq_of_nhds
  rw [← h'₁.continuousAt.eventuallyEq_nhd_iff_eventuallyEq_nhdNE h₁.continuousAt]
  filter_upwards [h₃, h'₃, self_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [← sub_eq_zero]
  rwa [h₂y, ← sub_eq_zero, ← smul_sub, smul_eq_zero_iff_right] at h₁y
  simp_all [zpow_ne_zero, sub_ne_zero]

lemma leadCoefficient_def₁ {g : 𝕜 → E} {n : ℤ}
    (h₁ : AnalyticAt 𝕜 g x)
    (h₂ : g x ≠ 0)
    (h₃ : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n • g z) :
    leadCoefficient f x = g x := by
  have h₄ : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h₃]
    fun_prop
  have : h₄.order = n := by
    apply h₄.order_eq_int_iff.2
    simp only [ne_eq, zpow_natCast]
    use g, h₁, h₂
    exact h₃
  apply leadCoefficient_def₀ h₁ h₄ (by simp [this]) (by simp_all [this])
