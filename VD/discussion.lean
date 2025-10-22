import Mathlib

open Function MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {x : 𝕜}
  {ι : Type*} {F : ι → 𝕜 → 𝕜}

namespace MeromorphicAt

theorem test₁ : MeromorphicAt (∏ n ∈ ∅, F n) x := by
  rw [Finset.prod_empty]
  -- At this stage, we have the goal `MeromorphicAt 1 x`, where the symbol `1`
  -- really means `One.toOfNat1 : 𝕜 → 𝕜`. Mathlib knows that constant
  -- functions are analytic/meromorphic, but cannot match the symbol `1` with
  -- the constant function `fun _ ↦ 𝕜 : 𝕜 → 𝕜`. Therefore neither `simp` nor
  -- `fun_prop` can close the goal at this point.
  sorry

-- This lemma is in a form that allows matching `1` with the constant function.
@[fun_prop, simp]
lemma ofNat (n : ℕ) (x : 𝕜) : MeromorphicAt (ofNat(n) : 𝕜 → 𝕜) x :=
  analyticAt_const.meromorphicAt

-- With the lemma above in place, the following now compiles fine, both using
-- `simp` or `fun_prop`.
theorem test₂ : MeromorphicAt (∏ n ∈ ∅, F n) x := by
  simp
