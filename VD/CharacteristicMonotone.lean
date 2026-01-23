import VD.Cartan

open Function Metric Real Set Classical Topology ValueDistribution


namespace ValueDistribution

/--
The characteristic function is monotone.

Note: Given that the proximity function is not monotone in general, this is a
surprisingly non-trivial consequence of Cartan's theorem,
`characteristic_top_eq_circleAverage_logCounting_add_const`.
-/
theorem characteristic_monotoneOn {f : ℂ → ℂ} (h : Meromorphic f) :
    MonotoneOn (characteristic f ⊤) (Ioi 0) := by
  intro a ha b hb hab
  obtain ⟨c, hc⟩ := characteristic_top_eq_circleAverage_logCounting_add_const h
  rw [hc a, hc b]
  gcongr
  · apply logCounting_circleIntegrable h
  · apply logCounting_circleIntegrable h
  · apply logCounting_monotoneOn ha hb hab
  · aesop
  · aesop

end ValueDistribution
