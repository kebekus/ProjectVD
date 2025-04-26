import Mathlib.Analysis.Meromorphic.Order
import VD.ToMathlib.MeromorphicAt_order

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {x : 𝕜}

noncomputable def leadCoefficient (f : 𝕜 → E) (x : 𝕜) : E := by
  by_cases h₁ : ¬MeromorphicAt f x
  · exact 0
  rw [not_not] at h₁
  by_cases h₂ : h₁.order = ⊤
  · exact 0
  exact (h₁.order_ne_top_iff.1 h₂).choose x
