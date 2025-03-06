import Mathlib.Analysis.Analytic.Order

open scoped Interval Topology
open Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f₁ f₂ : 𝕜 → E} {z₀ : 𝕜}

theorem AnalyticAt.order_congr (hf₁ : AnalyticAt 𝕜 f₁ z₀) (h : f₁ =ᶠ[𝓝 z₀] f₂):
    (hf₁.congr h).order = hf₁.order := by
  -- Trivial case: f vanishes identially around z₀
  by_cases h₁f₁ : hf₁.order = ⊤
  · rw [h₁f₁, order_eq_top_iff]
    filter_upwards [hf₁.order_eq_top_iff.1 h₁f₁, h]
    intro a h₁a h₂a
    rwa [← h₂a]
  -- General case
  lift hf₁.order to ℕ using h₁f₁ with n hn
  rw [eq_comm] at hn
  rw [AnalyticAt.order_eq_nat_iff] at *
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := hn
  use g, h₁g, h₂g
  filter_upwards [h, h₃g]
  intro a h₁a h₂a
  rw [← h₂a, h₁a]

theorem AnalyticAt.order_add₁ (hf₁ : AnalyticAt 𝕜 f₁ z₀) (hf₂ : AnalyticAt 𝕜 f₂ z₀)
    (h : hf₁.order < hf₂.order) :
    (hf₁.add hf₂).order = hf₁.order := by
  -- Trivial case: f₂ vanishes identically around z₀
  by_cases h₁f₂ : hf₂.order = ⊤
  · apply AnalyticAt.order_congr hf₁
    filter_upwards [hf₂.order_eq_top_iff.1 h₁f₂]
    intro a h₁a
    simp [h₁a]
  -- General case
  lift hf₂.order to ℕ using h₁f₂ with n₂ hn₂
  lift hf₁.order to ℕ using h.ne_top with n₁ hn₁
  rw [Nat.cast_lt] at h
  rw [eq_comm] at hn₁ hn₂
  rw [AnalyticAt.order_eq_nat_iff] at *
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := hn₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := hn₂
  use g₁ + (· - z₀) ^ (n₂ - n₁) • g₂
  constructor
  · apply h₁g₁.add
    apply AnalyticAt.smul _ h₁g₂
    apply AnalyticAt.pow
    fun_prop
  · constructor
    · simpa [Nat.sub_ne_zero_iff_lt.mpr h]
    · filter_upwards [h₃g₁, h₃g₂]
      intro a h₁a h₂a
      simp only [Pi.add_apply, h₁a, h₂a, Pi.smul_apply', Pi.pow_apply, smul_add, ← smul_assoc,
        smul_eq_mul, add_right_inj]
      rw [← pow_add, add_comm, eq_comm, Nat.sub_add_cancel (Nat.le_of_succ_le h)]

theorem AnalyticAt.order_add₂ (hf₁ : AnalyticAt 𝕜 f₁ z₀) (hf₂ : AnalyticAt 𝕜 f₂ z₀)
    (h : hf₁.order ≠ hf₂.order) :
    (hf₁.add hf₂).order = min hf₁.order hf₂.order := by
  by_cases h₁ : hf₁.order < hf₂.order
  · rw [min_eq_left (le_of_lt h₁)]
    exact hf₁.order_add₁ hf₂ h₁
  · rw [min_eq_right (le_of_not_lt h₁)]
    simp_rw [AddCommMagma.add_comm f₁ f₂]
    exact hf₂.order_add₁ hf₁ (lt_of_le_of_ne (le_of_not_lt h₁) h.symm)
