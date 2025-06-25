import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

variable
  {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {x : E} {f : E → F} {n : ℕ} {s : Set E}

open ContinuousMultilinearMap Topology

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
    use (Algebra.algebraMap ∘ c), d
    constructor
    · use a
    · constructor
      · intro β hβ
        apply Filter.mem_map.mpr
        apply Filter.mem_atTop_sets.mpr
        let γ : Set 𝕜 := (Algebra.algebraMap)⁻¹' β
        have hγ :  γ ∈ Bornology.cobounded 𝕜 := by
          rw [← Bornology.isCobounded_def, Metric.isCobounded_iff_closedBall_compl_subset 0]
          sorry
        have h₂γ := h₁ hγ
        rw [Filter.mem_map, Filter.mem_atTop_sets] at h₂γ
        obtain ⟨n, hn⟩ := h₂γ
        use n
        intro b hb
        simp_all
        have := hn b hb
        tauto
      · sorry
  · sorry
