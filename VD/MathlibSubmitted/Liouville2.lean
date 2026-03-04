import Mathlib.Analysis.Complex.Harmonic.Liouville

open Complex Real Set
set_option backward.isDefEq.respectTransparency false

variable
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {𝕜₂ : Type u_2} [NontriviallyNormedField 𝕜₂]
  {E : Type u_4} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type u_5} [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/--
Continuous linear maps are locally bounded. In other words, they map bounded
sets to bounded sets.
-/
instance : LocallyBoundedMapClass (E →SL[σ₁₂] F) E F where
  comap_cobounded_le := by
    intro ℓ
    rw [Bornology.comap_cobounded_le_iff]
    intro s hs
    obtain ⟨M, hM⟩ := hs.exists_norm_le
    rw [isBounded_iff_forall_norm_le]
    use ‖ℓ‖ * M
    intro y hy
    obtain ⟨σ, hσ⟩ := (mem_image _ _ _).1 hy
    calc ‖y‖
      _ ≤ ‖ℓ σ‖ := by rw [hσ.2]
      _ ≤ ‖ℓ‖ * ‖σ‖ := ContinuousLinearMap.le_opNorm ℓ σ
      _ ≤ ‖ℓ‖ * M := mul_le_mul (by rfl) (hM σ hσ.1) (norm_nonneg σ) (norm_nonneg ℓ)

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-
**Liouville's theorem for harmonic functions on the complex plane** A real-valued, bounded harmonic
function on the complex plane is constant.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant' (f : ℂ → E)
    (h_harm : HarmonicOnNhd f univ) (h_bound : Bornology.IsBounded (range f)) :
    ∀ z w, f z = f w := by
  intro z w
  obtain ⟨ℓ, h₁ℓ, h₂ℓ⟩ := exists_dual_vector'' ℝ (f z - f w)
  rw [map_sub, RCLike.ofReal_real_eq_id, id_eq] at h₂ℓ
  have η₁ : Bornology.IsBounded (range (ℓ ∘ f)) := by
    simpa [(by aesop : range (ℓ ∘ f) = ℓ '' range f)] using Bornology.IsBounded.image ℓ h_bound
  rw [← sub_eq_zero, ← norm_eq_zero, ← h₂ℓ]
  grind [bounded_harmonic_on_complex_plane_is_constant (ℓ ∘ f) (h_harm.comp_CLM ℓ) η₁]
