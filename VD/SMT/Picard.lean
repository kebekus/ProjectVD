/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# Picard's Little Theorem — SMT work package H

See `VD/SMT/PLAN-SecondMainTheorem.md`, §10.

Mathlib target: new file `Mathlib/Analysis/Complex/Picard.lean` (Picard's little theorem
is currently absent from Mathlib).
Dependencies: `VD/SMT/SecondMainTheorem.lean` (package F) and the pending
`VD/MathlibPending/CharacteristicIsBigOLog.lean` (characterization of rational functions
by characteristic growth).

Planned contents:

- H1, `MonotoneOn.isBigO_log_of_eventually_le`: filter-to-`atTop` transfer — a monotone
  function bounded by `C·log` for large `r` outside a set of finite measure is `O(log)`
  along `atTop` outright. (Same measure-theoretic device as the Borel growth lemma in
  `VD/MathlibSubmitted/BorelGrowth.lean`, but simpler.)

- H2, `ValueDistribution.Omits`: the omission predicate for values in `ℂ ∪ {∞}`, phrased
  through meromorphic orders (robust under junk values), with the bridge lemmas
  `Omits.of_forall_ne` and `Omits.truncatedLogCounting_eq_zero`; then
  `ValueDistribution.eventuallyConst_of_omits`: **Picard's little theorem, meromorphic
  version** — a meromorphic function on `ℂ` omitting three values of `ℂ ∪ {∞}` is
  constant away from a discrete set. Proof: the Second Main Theorem forces
  `T(r) = O(log r)`, so `f` is rational, and a rational function omitting three values is
  constant (fundamental theorem of algebra).

- H3, `Differentiable.exists_eq_const_of_forall_ne`: **Picard's little theorem, entire
  version** — an entire function omitting two finite values is constant.
-/
