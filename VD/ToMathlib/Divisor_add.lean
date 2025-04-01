import Mathlib.Analysis.Meromorphic.Divisor


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {z₀ : 𝕜} {U : Set 𝕜}

/-- Analytic functions have non-negative divisors. -/
theorem AnalyticOnNhd.divisor_nonneg [CompleteSpace E] (hf : AnalyticOnNhd 𝕜 f U) :
    0 ≤ MeromorphicOn.divisor f U := by
  intro x
  by_cases hx : x ∈ U
  · simp [hf.meromorphicOn, hx, (hf x hx).meromorphicAt_order_nonneg]
  simp [hx]

/-- Adding an analytic function to a meromorphic one does not change the pole divisor. -/
theorem MeromorphicOn.divisor_add_analytic [CompleteSpace E] (hf : MeromorphicOn f U)
    (hg : AnalyticOnNhd 𝕜 g U) :
    (divisor f U)⁻ = (divisor (f + g) U)⁻ := by
  ext x
  by_cases hx : x ∈ U
  · simp [negPart_def, hx, hf, hf.add hg.meromorphicOn]
    by_cases h : 0 ≤ (hf x hx).order
    · simp only [Int.neg_nonpos_iff_nonneg, WithTop.untop₀_nonneg, h, sup_of_le_right,
        right_eq_sup]
      calc 0
      _ ≤ min (hf x hx).order (hg.meromorphicOn x hx).order := by
        exact le_inf_iff.2 ⟨h, (hg x hx).meromorphicAt_order_nonneg⟩
      _ ≤ ((hf.add hg.meromorphicOn) x hx).order := by
        exact (hf x hx).order_add (hg x hx).meromorphicAt
    · simp at h
      rw [(hf x hx).order_add_of_order_lt_order (hg.meromorphicOn x hx)]
      calc (hf x hx).order
      _ < 0 := h
      _ ≤ (hg.meromorphicOn x hx).order := (hg x hx).meromorphicAt_order_nonneg
  simp [hx]
