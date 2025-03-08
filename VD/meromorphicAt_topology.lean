import Mathlib.Analysis.Meromorphic.Order

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {z₀ : 𝕜}

lemma bar (c : ℝ) (hc : 0 < c) : Tendsto (fun (x : 𝕜) ↦ ‖x⁻¹‖ * c) (𝓝[≠] 0) atTop := by
  apply Filter.Tendsto.comp (f := fun x ↦ ‖x⁻¹‖) (g := fun x ↦ x * c) (y := atTop)
  · apply Filter.tendsto_atTop_atTop_of_monotone
    · apply monotone_mul_right_of_nonneg
      linarith
    · intro b
      use b * c⁻¹
      rw [mul_assoc]
      field_simp
  · apply NormedField.tendsto_norm_inv_nhdsNE_zero_atTop

lemma hoge (f : E) : (map Norm.norm (𝓝 f)).HasBasis
    (fun ε ↦ 0 < ε) (fun ε ↦ Norm.norm '' {y | ‖y - f‖ < ε}) := by
  apply Filter.HasBasis.map
  exact NormedAddCommGroup.nhds_basis_norm_lt f

lemma foo (f : E) : Disjoint atTop (map Norm.norm (𝓝 f)) := by
  rw [Filter.HasBasis.disjoint_iff Filter.atTop_basis (hoge f)]
  use ‖f‖ + 1
  constructor
  · simp
  · use 1
    constructor
    · simp
    · rw [Set.disjoint_iff_inter_eq_empty]
      ext x
      constructor
      · intro h
        simp at h
        obtain ⟨x₁, hx₁, hx₂⟩ := h.2
        have : ‖x₁‖ ≤ ‖f‖ + ‖x₁ - f‖ := by apply norm_le_insert'
        linarith
      · intro h
        simp at h

lemma baz (e : E) (f : E) (he : e ≠ 0) : ¬(Tendsto (fun (x : 𝕜) ↦ x⁻¹ • e) (𝓝[≠] 0) (𝓝 f)) := by
  intro h
  let F := (fun (x : 𝕜) ↦ x⁻¹ • e)
  have h₀ : Tendsto (norm ∘ F) (𝓝[≠] 0) ((𝓝 f).map norm) := by
    intro U hU
    simp
    exact mem_of_superset (h hU) fun _ a ↦ a
  have h₁ : (norm ∘ F) = (fun (x : 𝕜) ↦ ‖x⁻¹‖ * ‖e‖) := by
    funext x
    simp
    rw [norm_smul]
    simp
  rw [h₁] at h₀
  have h₂ := bar (𝕜 := 𝕜) ‖e‖ (norm_pos_iff.mpr he)
  have h₃ : map (fun (x : 𝕜) ↦ ‖x⁻¹‖ * ‖e‖) (𝓝[≠] 0) ≤ (𝓝 f).map norm := by apply h₀
  have h₆ := foo f h₂ h₃
  simp at h₆
  have := NormedField.nhdsNE_neBot (0 : 𝕜)
  rw [h₆] at this
  have : ¬(⊥ : Filter 𝕜).NeBot := (Filter.not_neBot (f := ⊥)).mpr rfl
  contradiction

lemma fuga (hf : MeromorphicAt f z₀) (fneg : hf.order < 0) (h : ∃ (g : 𝕜 → E), ContinuousAt g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g) : False := by
  let n := (hf.order).untop (by exact LT.lt.ne_top fneg)
  have h₀ : hf.order = n := by simp [n]
  have h₁ := (MeromorphicAt.order_eq_int_iff hf n).mp h₀
  obtain ⟨g, hg, hfg⟩ := h
  obtain ⟨h, hh₁, hh₂, hfh⟩ := h₁
  have h₂ : g =ᶠ[𝓝[≠] z₀] (fun z ↦ (z - z₀) ^ n • h z) := Filter.EventuallyEq.trans hfg.symm hfh
  have h₃ : Tendsto g (𝓝 z₀) (𝓝 (g z₀)) := hg
  have h₄ : Tendsto (fun z ↦ (z - z₀) ^ n • h z) (𝓝[≠] z₀) (𝓝 (g z₀)) := Filter.Tendsto.congr' h₂ (tendsto_nhdsWithin_of_tendsto_nhds hg)
  have h₅ : ¬(Tendsto (fun z ↦ (z - z₀) ^ n • h z) (𝓝[≠] z₀) (𝓝 (g z₀))) := by sorry
  contradiction

/-- A meromorphic function has non-negative order if there exists a continuous extension. -/
theorem MeromorphicAt.order_nonneg_if_exists_continuous_extension (hf : MeromorphicAt f z₀)
    (h : ∃ (g : 𝕜 → E), ContinuousAt g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g) : 0 ≤ hf.order := by
  by_contra h₀
  push_neg at h₀
  exact fuga hf h₀ h

/-- A meromorphic function has non-negative order then there exists an analytic extension. -/
theorem MeromorphicAt.exists_analytic_extension_if_order_nonneg (hf : MeromorphicAt f z₀) (nneg : 0 ≤ hf.order) :
    ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
  by_cases h' : hf.order = ⊤
  · use 0
    constructor
    · apply analyticAt_const
    · rw [order_eq_top_iff] at h'
      exact h'
  · have h'' : hf.order < ⊤ := by exact WithTop.lt_top_iff_ne_top.mpr h'
    let n := (hf.order).untop (by exact LT.lt.ne_top h'')
    have h₀ : hf.order = n := by simp [n]
    have h₁ := (MeromorphicAt.order_eq_int_iff hf n).mp h₀
    obtain ⟨g, hg, hfg⟩ := h₁
    use (fun z ↦ (z - z₀) ^ n • g z)
    constructor
    · apply AnalyticAt.smul'
      · rw [h₀] at nneg
        simp at nneg
        have : ∃ (a : ℕ), n = ↑a := by apply Int.eq_ofNat_of_zero_le (by exact nneg)
        obtain ⟨a, ha⟩ := this
        rw [ha]
        simp
        apply AnalyticAt.pow
        apply AnalyticAt.sub'
        apply analyticAt_id
        apply analyticAt_const
      · exact hg
    · exact hfg.2

/-- A meromorphic function has non-negative order iff there exists a continuous extension. -/
theorem MeromorphicAt.order_nonneg_iff_exists_continuous_extension (hf : MeromorphicAt f z₀) :
    0 ≤ hf.order ↔ ∃ (g : 𝕜 → E), ContinuousAt g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
  constructor <;> intro h
  · obtain ⟨g, hg, hfg⟩ := MeromorphicAt.exists_analytic_extension_if_order_nonneg hf h
    use g
    exact ⟨hg.continuousAt, hfg⟩
  · apply MeromorphicAt.order_nonneg_if_exists_continuous_extension hf h

/-- A meromorphic function has non-negative order iff there exists an analytic extension. -/
theorem MeromorphicAt.order_nonneg_iff_exists_analytic_extension (hf : MeromorphicAt f z₀) :
    0 ≤ hf.order ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
  constructor <;> intro h
  · apply MeromorphicAt.exists_analytic_extension_if_order_nonneg hf h
  · obtain ⟨g, hg₁, hg₂⟩ := h
    rw [MeromorphicAt.order_nonneg_iff_exists_continuous_extension]
    use g
    exact ⟨hg₁.continuousAt, hg₂⟩
