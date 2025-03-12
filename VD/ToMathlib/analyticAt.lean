import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order

open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}

variable {𝕝 : Type*} [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕝 F] [IsScalarTower 𝕜 𝕝 F]

theorem AnalyticAt.localIdentity (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
(hfg : f =ᶠ[𝓝[≠] z₀] g) :
    f =ᶠ[𝓝 z₀] g := by
  rcases ((hf.sub hg).eventually_eq_zero_or_eventually_ne_zero) with h | h
  · exact Filter.eventuallyEq_iff_sub.2 h
  · simpa using (Filter.eventually_and.2 ⟨Filter.eventuallyEq_iff_sub.mp hfg, h⟩).exists
