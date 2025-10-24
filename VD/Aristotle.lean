import Mathlib.Analysis.Meromorphic.Basic

open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem MeromorphicAt.sum {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    MeromorphicAt (∑ n ∈ s, f n) x := by
  sorry
