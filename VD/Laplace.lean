import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def Real.Laplace' (f : E → ℝ) : E → ℝ := by
  intro z
  let T := (iteratedFDeriv ℝ 2 f z)
  --let τ := PiTensorProduct.lift T
  exact ∑ i, (iteratedFDeriv ℝ 2 f z) ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
