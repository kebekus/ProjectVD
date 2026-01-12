import VD.Cartan
import VD.MathlibPending.FunctionalProperties
import Mathlib

open Function Metric Real Set Classical Topology ValueDistribution


namespace ValueDistribution

/--
The characteristic function is monotonous.

Note: Given that the proximity function is not monotonous in general, this is a
surprisingly non-trivial consequence of Cartan's theorem,
`characteristic_top_eq_circleAverage_logCounting_add_const`.
-/
theorem characteristic_monotoneOn {f : ℂ → ℂ} (h : Meromorphic f) :
    MonotoneOn (characteristic f ⊤) (Ioi 0) := by
  obtain ⟨c, hc⟩ := characteristic_top_eq_circleAverage_logCounting_add_const h
  intro a ha b hb hab
  rw [hc a, hc b]
  gcongr
  · apply logCounting_circleIntegrable h
  · apply logCounting_circleIntegrable h
  · apply logCounting_monotoneOn ha hb hab
  · aesop
  · aesop

end ValueDistribution
