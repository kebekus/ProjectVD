import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

variable
  {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {x : E} {s : Set E}

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
Given `x ∈ s` and a field extension `𝕜 ⊆ 𝕜'`, the tangent of `s` at `x` with
respect to `𝕜` is contained in the tangent of `s` at `x` with respect to `𝕜'`.
-/
theorem tangentConeAt_mono_field : tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜' s x := by
  intro α hα
  simp [tangentConeAt] at hα ⊢
  obtain ⟨c, d, ⟨a, h₁a⟩, h₁, h₂⟩ := hα
  use ((algebraMap 𝕜 𝕜') ∘ c), d
  constructor
  · use a
  · constructor
    · intro β hβ
      rw [Filter.mem_map, Filter.mem_atTop_sets]
      obtain ⟨n, hn⟩ := Filter.mem_atTop_sets.1 (Filter.mem_map.1 (h₁ (algebraMap_cobounded_le_cobounded (𝕜' := 𝕜') hβ)))
      use n, fun _ _ ↦ by simp_all
    · simpa

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
  <;> simp [Submodule.span_mono tangentConeAt_mono_field]

/--
Assume that `E` is a normed vector space over normed fields `𝕜 ⊆ 𝕜'` and all
points of `s` are points of unique differentiability with respect to the smaller
field `𝕜`, then they are also points of unique differentiability with respect
to the larger field `𝕜`.
-/
theorem UniqueDiffOn.mono_field (h₂s : UniqueDiffOn 𝕜 s) :
    UniqueDiffOn 𝕜' s := fun x hx ↦ (h₂s x hx).mono_field
