/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

Your Lean code is run in a custom environment, which uses these headers:

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

The following was proved by Aristotle:

- @[fun_prop]
theorem MeromorphicAt.sum {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    MeromorphicAt (∑ n ∈ s, f n) x
-/

import Mathlib.Analysis.Meromorphic.Basic


open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem MeromorphicAt.sum {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    MeromorphicAt (∑ n ∈ s, f n) x := by
  -- By induction on the finite set s, we can show that the sum of the functions in s is meromorphic at x.
  induction' s using Finset.induction with σ s ih;
  · -- The zero function is meromorphic on the entire complex plane, so it is certainly meromorphic at x.
    simp [MeromorphicAt];
    exact analyticAt_const;
  · rename_i hs;
    rw [ Finset.sum_insert ih ] ; exact ( h σ ).add hs;