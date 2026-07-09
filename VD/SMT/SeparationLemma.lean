/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# The Separation Lemma — SMT work package C

See `VD/SMT/PLAN-SecondMainTheorem.md`, §5.

Mathlib target: extend `Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean`.
Dependencies: none (independently PR-able).

Planned contents: the pointwise **separation lemma** of value distribution theory, over a
general nontrivially normed field —

- `exists_sum_posLog_norm_inv_sub_le`: for a finite set `s` of points there is a constant
  `C` with `∑ a ∈ s, log⁺ ‖w - a‖⁻¹ ≤ log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ + C` for **all** `w`.

If `w` is close to one point `a₀` of `s` (within half the minimal gap), the singular term
`(w - a₀)⁻¹` dominates the sum, so the single function `‖∑ a ∈ s, (· - a)⁻¹‖` detects
closeness to *any* point of `s`; if `w` is far from all points of `s`, the left-hand side
is bounded by a constant. Thanks to Lean's junk-value convention `(0 : ℝ)⁻¹ = 0` the
statement holds for all `w` without exceptional points, which spares the integration step
in `VD/SMT/ProximityEstimates.lean` (package D) any codiscrete comparison.

This is the elementary input that lets the Second Main Theorem treat several target
values simultaneously.
-/
