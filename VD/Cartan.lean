import Mathlib

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution


namespace ValueDistribution

/--
Helper Lemma: The logarithmic counting function is circle integrable. The right
side of the equality in Cartan's theorem is therefore meaningful.
-/
lemma logCounting_circleIntegrable {r : ℝ} {f : ℂ → ℂ} (h : Meromorphic f) :
    CircleIntegrable (logCounting f · r) 0 1 := by
  sorry

/--
Cartan's theorem, qualitative version: Up to a constant, the characteristic
function for the poles of `f` equals a circle integral over the logarithmic
counting functions for the `z`-values of `f`, where `z` is the integration
variable.
-/
theorem characteristic_top_eq_circleAverage_logCounting_add_const {f : ℂ → ℂ} (h : Meromorphic f) :
    ∃ const, ∀ r ≠ 0, characteristic f ⊤ r = circleAverage (logCounting f · r) 0 1 + const := by
  sorry


end ValueDistribution
