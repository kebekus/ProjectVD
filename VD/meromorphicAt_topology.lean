import Mathlib.Analysis.Meromorphic.Order

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {z₀ : 𝕜}

/-- A meromorphic function has non-negative order iff there exists an analytic extension. -/
theorem MeromorphicAt.order_nonneg_iff_exists_analytic_extension (hf : MeromorphicAt f z₀) :
    0 ≤ hf.order ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
  constructor
  · sorry
  · sorry

/-- A meromorphic function has non-negative order iff there exists a continuous extension. -/
theorem MeromorphicAt.order_nonneg_iff_exists_continuous_extension (hf : MeromorphicAt f z₀) :
    0 ≤ hf.order ↔ ∃ (g : 𝕜 → E), ContinuousAt g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
  constructor
  · sorry
  · sorry


example : Tendsto (fun (x : ℝ) ↦ x⁻¹) (𝓝[>] 0) atTop := by
  apply tendsto_inv_nhdsGT_zero

lemma foo (c : ℝ) (hc : c > 0) : Tendsto (fun (x : ℝ) ↦ x⁻¹ * c) (𝓝[>] 0) atTop := by
  apply Filter.Tendsto.comp (f := fun x ↦ x⁻¹) (g := fun x ↦ x * c) (y := atTop)
  intro U hU
  simp
  rw [Filter.mem_atTop_sets] at hU
  obtain ⟨a, ha⟩ := hU
  use a * c⁻¹
  intro b hb
  apply ha
  rw [mul_inv_le_iff₀] at hb
  exact hb
  exact hc
  apply tendsto_inv_nhdsGT_zero

#check NormedField.tendsto_norm_inv_nhdsNE_zero_atTop
lemma bar (c : ℝ) (hc : c > 0) : Tendsto (fun (x : 𝕜) ↦ ‖x‖⁻¹ * c) (𝓝[≠] 0) atTop := by
  apply Filter.Tendsto.comp (f := fun x ↦ ‖x‖) (g := fun x ↦ x⁻¹ * c) (y := 𝓝[>] 0)
  apply foo c hc
  intro U hU
  rw [Filter.mem_map]
  rw [mem_nhdsWithin] at *
  obtain ⟨V, hV, hV₀, hVU⟩ := hU
  use (fun x ↦ ‖x‖) ⁻¹' V
  constructor
  · apply Continuous.isOpen_preimage
    exact continuous_norm
    exact hV
  · constructor
    · simp
      exact hV₀
    · intro x hx
      simp at *
      apply hVU
      constructor
      · exact hx.1
      · simp
        exact hx.2

lemma hoge (f : E) : (map Norm.norm (𝓝 f)).HasBasis
    (fun ε ↦ 0 < ε) (fun ε ↦ Norm.norm '' {y | ‖y - f‖ < ε}) := by
  apply Filter.HasBasis.map
  exact NormedAddCommGroup.nhds_basis_norm_lt f

def inv (x : 𝕜) (e : E) := x ^ (-(1 : ℤ)) • e

example (e : E) (f : E) (he : e ≠ 0) : ¬(Tendsto (fun (x : 𝕜) ↦ x ^ (-(1 : ℤ)) • e) (𝓝 0) (𝓝 f)) := by
  intro h
  have h₀ : Tendsto (norm ∘ (fun (x : 𝕜) ↦ inv x e)) (𝓝 (0 : 𝕜)) ((𝓝 f).map norm) := by
    intro U hU
    simp
    exact mem_of_superset (h hU) fun _ a ↦ a
  have h₁ : (Norm.norm ∘ fun x ↦ x ^ (-(1 : ℤ)) • e) = (fun (x : 𝕜) ↦ (norm x)⁻¹ * (norm e)) := by
    funext x
    simp
    rw [norm_smul]
    simp
  unfold inv at h₀
  rw [h₁] at h₀
  have h : ‖e‖ > 0 := by rw [gt_iff_lt, norm_pos_iff (a := e)]; exact he
  have h₂ := bar (𝕜 := 𝕜) (norm e) h
  have h₃ : map (fun (x : 𝕜) ↦ ‖x‖⁻¹ * ‖e‖) (𝓝[≠] 0) ≤ map Norm.norm (𝓝 f) := by
    calc
      map (fun (x : 𝕜) ↦ ‖x‖⁻¹ * ‖e‖) (𝓝[≠] 0) ≤ map (fun (x : 𝕜) ↦ ‖x‖⁻¹ * ‖e‖) (𝓝 0) := by
        apply GCongr.Filter.map_le_map
        apply nhdsWithin_le_nhds
      _ ≤ map Norm.norm (𝓝 f) := by
        apply h₀
  have h₅ : Disjoint atTop (map Norm.norm (𝓝 f)) := by
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
  have h₆ := h₅ h₂ h₃
  simp at h₆
  have := NormedField.punctured_nhds_neBot (0 : 𝕜)
  rw [h₆] at this
  have : ¬(⊥ : Filter 𝕜).NeBot := (Filter.not_neBot (f := ⊥)).mpr rfl
  contradiction
