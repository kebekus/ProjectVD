import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Mul

open TensorProduct Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-!
# Main File Starts Here
-/

variable (𝕜) in
/-- If two functions agree in a neighborhood, then so do their iterated derivatives. -/
theorem Filter.EventuallyEq.iteratedFDeriv
    {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) (n : ℕ) :
    iteratedFDeriv 𝕜 n f₁ =ᶠ[𝓝 x] iteratedFDeriv 𝕜 n f₂ := by
  simp_all [← nhdsWithin_univ, ← iteratedFDerivWithin_univ,
    Filter.EventuallyEq.iteratedFDerivWithin]

/-- Iterated derivatives commute with left composition by continuous linear equivalences- -/
theorem ContinuousLinearEquiv.iteratedFDeriv_comp_left {f : E → F} {x : E} (g : F ≃L[𝕜] G) {i : ℕ} :
    iteratedFDeriv 𝕜 i (g ∘ f) x =
      (g : F →L[𝕜] G).compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x) := by
  simp only [← iteratedFDerivWithin_univ]
  apply g.iteratedFDerivWithin_comp_left f uniqueDiffOn_univ trivial
