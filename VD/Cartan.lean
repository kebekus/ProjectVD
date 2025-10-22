import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem

open Function MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {x : 𝕜}
  {ι : Type*} {F : ι → 𝕜 → 𝕜}
