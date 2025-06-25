import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

variable
  {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {x : E} {s : Set E}

open ContinuousMultilinearMap Topology

/--
Filter version of the statement that preimages of cobounded sets under the
algebra map are cobounded.
-/
theorem algebraMap_cobounded_le_cobounded :
    Filter.map (algebraMap 𝕜 𝕜') (Bornology.cobounded 𝕜) ≤ Bornology.cobounded 𝕜' := by
  intro c hc
  rw [Filter.mem_map, ← Bornology.isCobounded_def, ← Bornology.isBounded_compl_iff,
    isBounded_iff_forall_norm_le]
  obtain ⟨s, hs⟩ := isBounded_iff_forall_norm_le.1
    (Bornology.isBounded_compl_iff.2 (Bornology.isCobounded_def.1 hc))
  use s
  exact fun x hx ↦ by simpa [norm_algebraMap] using hs ((algebraMap 𝕜 𝕜') x) hx

/--
Assume that `E` is a normed vector space over normed fields `𝕜 ⊆ 𝕜'` and that
`x ∈ s` is a point of unique differentiability with respect to the set `s` and
the smaller field `𝕜`, then `x` is also a point of unique differentiability
with respect to the set `s` and the larger field `𝕜`.
-/
theorem UniqueDiffWithinAt.mono_field (h₂s : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜' s x := by
  rw [uniqueDiffWithinAt_iff] at *
  simp_all only [and_true]
  apply Dense.mono _ h₂s.1
  trans ↑(Submodule.span 𝕜 (tangentConeAt 𝕜' s x))
  · apply Submodule.span_mono
    intro α hα
    simp [tangentConeAt] at hα ⊢
    obtain ⟨c, d, ⟨a, h₁a⟩, h₁, h₂⟩ := hα
    use ((algebraMap 𝕜 𝕜') ∘ c), d
    constructor
    · use a
    · constructor
      · intro β hβ
        apply Filter.mem_map.mpr
        apply Filter.mem_atTop_sets.mpr
        let γ : Set 𝕜 := (algebraMap 𝕜 𝕜')⁻¹' β
        have h₂γ := h₁ (algebraMap_cobounded_le_cobounded (𝕜' := 𝕜') hβ)
        rw [Filter.mem_map, Filter.mem_atTop_sets] at h₂γ
        obtain ⟨n, hn⟩ := h₂γ
        use n
        intro b hb
        simp_all
      · simpa
  · simp

/--
Assume that `E` is a normed vector space over normed fields `𝕜 ⊆ 𝕜'` and all
points of `s` are points of unique differentiability with respect to the smaller
field `𝕜`, then they are also points of unique differentiability with respect
to the larger field `𝕜`.
-/
theorem UniqueDiffOn.mono_field (h₂s : UniqueDiffOn 𝕜 s) :
    UniqueDiffOn 𝕜' s := fun x hx ↦ (h₂s x hx).mono_field
