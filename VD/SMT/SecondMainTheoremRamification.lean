/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# The Second Main Theorem with Ramification Term — SMT work package E

See `VD/SMT/PLAN-SecondMainTheorem.md`, §7.

Mathlib target: `Mathlib/Analysis/Complex/ValueDistribution/SecondMainTheorem.lean`
(part 2 of 3).
Dependencies: `VD/SMT/ProximityEstimates.lean` (package D); uses the First Main Theorem
and the Lemma on the Logarithmic Derivative.

Planned contents:

- S1, `ValueDistribution.secondMainTheorem_ramification`: **the Second Main Theorem** in
  Lang's form, for a meromorphic function `f` on `ℂ` and finitely many distinct finite
  targets `s : Finset ℂ`:
  `m(r, ∞) + Σₐ m(r, a) + N₁(r) ≤ 2·T(r) + c·(log⁺ T(r) + log r)` for all large `r`
  outside a set of finite Lebesgue measure (the filter `volume.cofinite ⊓ atTop`), where
  `N₁(r) = N(r, 1/f′) + 2·N(r, f) − N(r, f′)` is the ramification term. No nondegeneracy
  hypothesis: the eventually-constant case is handled internally via D1.

- `ValueDistribution.ramification_nonneg`: `0 ≤ N₁(r)` for `1 ≤ r`, so users may drop the
  ramification term.

- A posPart reformulation as an `IsBigO` statement along `volume.cofinite ⊓ atTop`, and a
  sanity `example`: for `f = Complex.exp` and `s = {0}` the inequality is sharp up to the
  error term.
-/
