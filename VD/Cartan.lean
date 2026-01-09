import VD.MathlibSubmitted.Nevanlinna_add_characteristic
--import Mathlib.MeasureTheory.Integral.Prod
import Mathlib

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution


namespace ValueDistribution

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
