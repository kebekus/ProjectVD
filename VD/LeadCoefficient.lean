import Mathlib.Analysis.Meromorphic.Order

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {x : 𝕜}


noncomputable def leadCoefficient (f : 𝕜 → E) (x : 𝕜) : E := by
  by_cases h : MeromorphicAt f x
  · exact 0
  · exact 0
