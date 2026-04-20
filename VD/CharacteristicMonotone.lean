/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

module

public import VD.Cartan

public section

/-!
# Monotonicity of the Characteristic Function

This file derives the monotonicity of `characteristic f ⊤` on `(0, ∞)` from Cartan's
formula.

## Main statements

- `ValueDistribution.characteristic_monotoneOn`

## References

* [S. Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677]

## Tags

characteristic function, monotonicity, Cartan formula
-/

namespace ValueDistribution

/-- The characteristic function is monotone on `(0, ∞)`.

Since the proximity function is not monotone in general, this is a nontrivial consequence of
`characteristic_top_eq_circleAverage_logCounting_add_circleAverage_log_trailingCoeff`. -/
theorem characteristic_monotoneOn {f : ℂ → ℂ} (h : Meromorphic f) :
    MonotoneOn (characteristic f ⊤) (Set.Ioi 0) := by
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
