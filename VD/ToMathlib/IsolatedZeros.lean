import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order

open Real Filter

/--
The set where an analytic function has zero or infinite order is discrete within
its domain of analyticity.
-/
theorem AnalyticOnNhd.codiscreteWithin_setOf_analyticOrderAt_eq_zero_or_top {f : ℝ → ℝ} {U : Set ℝ}
    (hf : AnalyticOnNhd ℝ f U) :
    {u : ℝ | analyticOrderAt f u = 0 ∨ analyticOrderAt f u = ⊤} ∈ codiscreteWithin U := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp [analyticOrderAt_eq_top, ha]
  · filter_upwards [h₁f] with a ha
    simp +contextual [(hf a _).analyticOrderAt_eq_zero, ha]

/--
If an analytic function `f` is not constantly zero on a connected set `U`, then
its set of zeros is codiscrete within `U`.
-/
theorem AnalyticOnNhd.preimage_zero_codiscreteWithin {f : ℝ → ℝ} {U : Set ℝ} {x : ℝ} (h₁f : AnalyticOnNhd ℝ f U) (h₂f : f x ≠ 0)
    (hU : IsConnected U) (hx : x ∈ U) :
    f ⁻¹' {0}ᶜ ∈ codiscreteWithin U := by
  filter_upwards [h₁f.codiscreteWithin_setOf_analyticOrderAt_eq_zero_or_top, self_mem_codiscreteWithin U] with a ha h₂a
  rw [← (h₁f x hx).analyticOrderAt_eq_zero] at h₂f
  have {u : U} : analyticOrderAt f u ≠ ⊤ := by
    apply (h₁f.exists_analyticOrderAt_ne_top_iff_forall hU).1
    use ⟨x, hx⟩
    simp_all
  rw [(h₁f a h₂a).analyticOrderAt_eq_zero] at ha
  simp_all

/--
If an analytic function `f` is not constantly zero on `𝕜`, then its set of
zeros is codiscrete.
-/
theorem AnalyticOnNhd.preimage_zero_codiscrete {f : ℝ → ℝ} {x : ℝ} (h₁f : AnalyticOnNhd ℝ f Set.univ) (hx : f x ≠ 0) :
    f ⁻¹' {0}ᶜ ∈ codiscrete ℝ :=
  h₁f.preimage_zero_codiscreteWithin hx isConnected_univ trivial
