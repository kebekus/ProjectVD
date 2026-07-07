/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# The Borel Growth Lemma — LLD work package D (theorem T2)

**Status: stub, no content yet.** See `VD/LLD/PLAN-LogarithmicDerivative.md`, §6.

Mathlib target: new file, suggested `Mathlib/MeasureTheory/Function/BorelGrowth.lean`
(maintainers may prefer another home). Pure real analysis / measure theory.
Dependencies: none (fully parallel to all other packages, independently PR-able).

Planned declaration:

- `MonotoneOn.eventually_le_two_mul` — **Borel's growth lemma**: for `S : ℝ → ℝ`
  monotone on `Set.Ici a` with `1 ≤ S` there,
  `∀ᶠ r in volume.cofinite ⊓ atTop, S (r + (S r)⁻¹) ≤ 2 * S r`.

Recommended proof (no recursion): Vitali covering. On the bad set
`E = {r | S (r + (S r)⁻¹) > 2 * S r}`, the function `g = log ∘ S` jumps by more than
`log 2` across each interval `[r, r + (S r)⁻¹]`. Apply
`Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall`; disjointness and
monotonicity force geometric decay of the interval lengths, so `volume E ≤ 10 < ∞`.
Fallback: classical greedy recursion (Hayman, *Meromorphic Functions*, Lemma 2.4).
-/
