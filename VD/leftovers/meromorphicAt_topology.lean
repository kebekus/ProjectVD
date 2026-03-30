import Mathlib.Analysis.Meromorphic.Order

open Filter Topology
set_option backward.isDefEq.respectTransparency false

lemma tendsto_nhdsWithin_of_tendsto_nhds' {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {a : α} {f : α → β}
    (hf : Tendsto f (𝓝 a) (𝓝 (f a))) (hfa : Set.MapsTo f {a}ᶜ {f a}ᶜ) :
    Tendsto f (𝓝[≠] a) (𝓝[≠] (f a)) :=
  ContinuousWithinAt.tendsto_nhdsWithin (tendsto_nhdsWithin_of_tendsto_nhds hf) hfa

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {z₀ : 𝕜}

/-- A meromorphic function has non-negative order if there exists a continuous extension. -/
theorem MeromorphicAt.order_nonneg_if_exists_continuous_extension (hf : MeromorphicAt f z₀)
    (h : ∃ (g : 𝕜 → E), ContinuousAt g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g) : 0 ≤ meromorphicOrderAt f z₀ := by
  by_contra h₀
  push Not at h₀
  set n := (meromorphicOrderAt f z₀).untop (by exact LT.lt.ne_top h₀) with h₁
  have h₁ : meromorphicOrderAt f z₀ = n := by simp [n]
  simp [h₁] at h₀
  have nneg : 0 < -n := by linarith
  obtain ⟨a, ha⟩ := Int.eq_succ_of_zero_lt nneg
  obtain ⟨g, hg, hfg⟩ := h
  obtain ⟨h, hh₁, hh₂, hfh⟩ := (meromorphicOrderAt_eq_int_iff hf).mp h₁
  have h₂ : Tendsto (fun z ↦ ‖(z - z₀) ^ n • h z‖) (𝓝[≠] z₀) (𝓝 ‖g z₀‖) := by
    apply tendsto_norm.comp
    exact (tendsto_nhdsWithin_of_tendsto_nhds hg).congr' (hfg.symm.trans hfh)
  apply not_tendsto_atTop_of_tendsto_nhds h₂
  have h₃ : (fun z ↦ ‖(z - z₀) ^ n • h z‖) =
      ((fun x ↦ ‖x⁻¹‖) ∘ (fun z ↦ (z - z₀) ^ a.succ)) * (fun z ↦ ‖h z‖) := by
    funext z
    simp [norm_smul, ← zpow_natCast, ← ha]
  rw [h₃]
  have h₄ : Tendsto ((fun x ↦ ‖x⁻¹‖) ∘ (fun z ↦ (z - z₀) ^ a.succ)) (𝓝[≠] z₀) atTop := by
    apply tendsto_norm_inv_nhdsNE_zero_atTop.comp (y := 𝓝[≠] 0)
    have hh₁ : ContinuousAt (fun z ↦ (z - z₀)) z₀ := by
      apply continuousAt_id.sub continuousAt_const
    have hh₂ : (z₀ - z₀) ^ a.succ = 0 := by simp
    rw [← hh₂]
    apply tendsto_nhdsWithin_of_tendsto_nhds' (hh₁.pow a.succ).tendsto
    intro x hx h
    simp [sub_eq_zero] at h
    apply hx h
  apply h₄.atTop_mul_pos (norm_pos_iff.mpr hh₂)
  apply tendsto_nhdsWithin_of_tendsto_nhds
  exact hh₁.continuousAt.norm

/-- If a meromorphic function has non-negative order then there exists an analytic extension. -/
theorem MeromorphicAt.exists_analytic_extension_if_order_nonneg (hf : MeromorphicAt f z₀)
    (nneg : 0 ≤ meromorphicOrderAt f z₀) :
    ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
  by_cases h' : meromorphicOrderAt f z₀ = ⊤
  · use 0
    exact ⟨analyticAt_const, meromorphicOrderAt_eq_top_iff.mp h'⟩
  · let n := (meromorphicOrderAt f z₀).untop (LT.lt.ne_top (WithTop.lt_top_iff_ne_top.mpr h'))
    have h₀ : meromorphicOrderAt f z₀ = n := by simp [n]
    obtain ⟨g, hg, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp h₀
    use (fun z ↦ (z - z₀) ^ n • g z)
    constructor
    · apply AnalyticAt.smul _ hg
      · simp [h₀] at nneg
        obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le nneg
        simp [ha]
        apply (analyticAt_id.sub analyticAt_const).pow
    · exact hfg.2

/-- A meromorphic function has non-negative order iff there exists a continuous extension. -/
theorem MeromorphicAt.order_nonneg_iff_exists_continuous_extension (hf : MeromorphicAt f z₀) :
    0 ≤ meromorphicOrderAt f z₀ ↔ ∃ (g : 𝕜 → E), ContinuousAt g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
  constructor <;> intro h
  · obtain ⟨g, hg, hfg⟩ := MeromorphicAt.exists_analytic_extension_if_order_nonneg hf h
    use g
    exact ⟨hg.continuousAt, hfg⟩
  · apply MeromorphicAt.order_nonneg_if_exists_continuous_extension hf h

/-- A meromorphic function has non-negative order iff there exists an analytic extension. -/
theorem MeromorphicAt.order_nonneg_iff_exists_analytic_extension (hf : MeromorphicAt f z₀) :
    0 ≤ meromorphicOrderAt f z₀ ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
  constructor <;> intro h
  · apply MeromorphicAt.exists_analytic_extension_if_order_nonneg hf h
  · obtain ⟨g, hg₁, hg₂⟩ := h
    rw [hf.order_nonneg_iff_exists_continuous_extension]
    use g
    exact ⟨hg₁.continuousAt, hg₂⟩
