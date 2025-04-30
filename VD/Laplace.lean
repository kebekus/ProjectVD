import Mathlib.Analysis.Complex.Basic
import VD.partialDeriv

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

noncomputable def Complex.laplace2 (f : ℂ → F) : ℂ → F :=
  partialDeriv ℝ 1 (partialDeriv ℝ 1 f) + partialDeriv ℝ Complex.I (partialDeriv ℝ Complex.I f)
