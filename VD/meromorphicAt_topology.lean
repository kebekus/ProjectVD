import Mathlib.Analysis.Meromorphic.Order

open Filter Topology

section

#loogle Filter.HasBasis

variable {α β ι : Type*} (x : α) (f : α → β) (p : ι → Prop) (s : ι → Set β)
    [Preorder β] [Preorder α] [TopologicalSpace α]
    [IsDirected α fun x1 x2 ↦ x1 ≤ x2] [IsDirected β fun x1 x2 ↦ x1 ≤ x2]
    [Nonempty α] [Nonempty β]

example (h : HasBasis (map f (𝓝 x)) p s) (h' : ∃ i', p i') :
    Disjoint atTop ((𝓝 x).map f) := by
  rw [Filter.HasBasis.disjoint_iff Filter.atTop_basis h]
  use (f x)
  constructor
  · simp
  · obtain ⟨i', hi'⟩ := h'
    use i'
    constructor
    · exact hi'
    · rw [Set.disjoint_iff_inter_eq_empty]
      ext y
      constructor
      · intro hh
        simp at hh
        sorry
      · exact fun a ↦ False.elim a

end

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {z₀ : 𝕜}

lemma bar {c : ℝ} (hc : 0 < c) : Tendsto (fun (x : 𝕜) ↦ ‖x⁻¹‖ * c) (𝓝[≠] 0) atTop := by
  apply Filter.Tendsto.comp (f := fun x ↦ ‖x⁻¹‖) (g := fun x ↦ x * c) (y := atTop)
  · apply Filter.tendsto_atTop_atTop_of_monotone
    · apply monotone_mul_right_of_nonneg (by linarith)
    · intro b
      use b * c⁻¹
      field_simp [mul_assoc]
  · apply NormedField.tendsto_norm_inv_nhdsNE_zero_atTop

lemma hoge (f : E) : ((𝓝 f).map norm).HasBasis
    (fun ε ↦ 0 < ε) (fun ε ↦ norm '' {y | ‖y - f‖ < ε}) :=
  Filter.HasBasis.map _ (NormedAddCommGroup.nhds_basis_norm_lt _)

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
      · exact fun a ↦ False.elim a

lemma baz (e : E) (f : E) (he : e ≠ 0) : ¬(Tendsto (fun (x : 𝕜) ↦ x⁻¹ • e) (𝓝[≠] 0) (𝓝 f)) := by
  intro h
  have h₀ : Tendsto (fun (x : 𝕜) ↦ ‖x⁻¹‖ * ‖e‖) (𝓝[≠] 0) ((𝓝 f).map norm) := by
    have : (norm ∘ (fun (x : 𝕜) ↦ x⁻¹ • e)) = (fun (x : 𝕜) ↦ ‖x⁻¹‖ * ‖e‖) := by
      funext x
      simp [norm_smul]
    rw [← this]
    intro U hU
    rw [← Filter.map_compose]
    exact h hU
  have h₂ := bar (𝕜 := 𝕜) (norm_pos_iff.mpr he)
  have h₆ := foo f h₂ h₀
  rw [le_bot_iff, Filter.map_eq_bot_iff] at h₆
  have := NormedField.nhdsNE_neBot (0 : 𝕜)
  exact Filter.NeBot.ne' h₆

#loogle Filter.Tendsto, "smul"
lemma fuga (hf : MeromorphicAt f z₀) (fneg : hf.order < 0)
    (h : ∃ (g : 𝕜 → E), ContinuousAt g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g) : False := by
  let n := (hf.order).untop (by exact LT.lt.ne_top fneg)
  have h₀ : hf.order = n := by simp [n]
  obtain ⟨g, hg, hfg⟩ := h
  obtain ⟨h, hh₁, hh₂, hfh⟩ := (hf.order_eq_int_iff n).mp h₀
  -- have h₃ : Tendsto g (𝓝 z₀) (𝓝 (g z₀)) := hg
  have h₄ : Tendsto (fun z ↦ (z - z₀) ^ n • h z) (𝓝[≠] z₀) (𝓝 (g z₀)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds hg).congr' (hfg.symm.trans hfh)
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
    exact ⟨analyticAt_const, hf.order_eq_top_iff.mp h'⟩
  · let n := (hf.order).untop (LT.lt.ne_top (WithTop.lt_top_iff_ne_top.mpr h'))
    have h₀ : hf.order = n := by simp [n]
    obtain ⟨g, hg, hfg⟩ := (hf.order_eq_int_iff n).mp h₀
    use (fun z ↦ (z - z₀) ^ n • g z)
    constructor
    · apply AnalyticAt.smul' _ hg
      · simp [h₀] at nneg
        obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le nneg
        simp [ha]
        apply AnalyticAt.pow (AnalyticAt.sub' analyticAt_id analyticAt_const)
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
