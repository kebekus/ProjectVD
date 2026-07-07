/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

/-!
# The Differentiated Poisson–Jensen Formula — LLD work package B6

**Status: stub, no content yet.** See `VD/LLD/PLAN-LogarithmicDerivative.md`, §4.

Mathlib target: new file `Mathlib/Analysis/Complex/PoissonJensenDeriv.lean`.
Dependencies: `MeromorphicLogDeriv.lean`, `PoissonSchwarzDeriv.lean`.

Planned declaration:

- `MeromorphicOn.logDeriv_eqOn_codiscrete` — **differentiated Poisson–Jensen formula**:
  for `f` meromorphic on `closedBall 0 R` with order `≠ ⊤` everywhere,
  ```
  logDeriv f =ᶠ[codiscreteWithin (ball 0 R)]
    fun w ↦ circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • Real.log ‖f ζ‖) 0 R
      - ∑ᶠ a, (divisor f (ball 0 R) a) • logDeriv (canonicalFactor R a) w
  ```
  Sign check (`f = id`, `R = 1`): `divisor = δ₀`, `canonicalFactor 1 0 = (·)⁻¹`,
  kernel term `= 0`, RHS `= -(-1/w) = 1/w`. ✓

Proof plan: mirror `poissonJensen₀` in `VD/MathlibPending/PoissonJensen.lean` —
take the extended canonical decomposition (`exists_ecanonicalDecomp`), apply the
codiscrete `logDeriv` arithmetic from work package A, rewrite `logDeriv h` via B4;
on the sphere the canonical-factor terms vanish
(`norm_canonicalFactor_eval_circle_eq_one`) and each sphere-divisor term integrates
to `(w - u)⁻¹` (B4 special case), cancelling exactly.
-/
