import VD.Cartan

open Function Metric Real Set Classical Topology ValueDistribution

namespace ValueDistribution

/--
The characteristic function is monotone.

Note: Given that the proximity function is not monotone in general, this is a
surprisingly non-trivial consequence of Cartan's formula.
-/
theorem characteristic_monotoneOn {f : ℂ → ℂ} (h : Meromorphic f) :
    MonotoneOn (characteristic f ⊤) (Ioi 0) := by
  intro a ha b hb hab
  rw [characteristic_top_eq_circleAverage_logCounting_add_circleAverage_log_trailingCoeff
      ha.ne' h]
  rw [characteristic_top_eq_circleAverage_logCounting_add_circleAverage_log_trailingCoeff
      hb.ne' h]
  gcongr
  · apply circleIntegrable_logCounting h
  · apply circleIntegrable_logCounting h
  · apply logCounting_monotoneOn ha hb hab

end ValueDistribution
