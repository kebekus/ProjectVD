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



@[to_additive]
theorem leOnePart_min {α : Type*} [Lattice α] [Group α] [MulLeftMono α] [MulRightMono α] (a b : α) :
    (min a b)⁻ᵐ = max a⁻ᵐ b⁻ᵐ := by
  simp [leOnePart, inv_inf]
  exact sup_sup_distrib_right a⁻¹ b⁻¹ 1

@[to_additive]
theorem leOnePart_max {α : Type*} [DistribLattice α] [Group α] [MulLeftMono α] [MulRightMono α] (a b : α) :
    (max a b)⁻ᵐ = min a⁻ᵐ b⁻ᵐ := by
  simp [leOnePart, inv_sup, sup_inf_right]

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*} [AddCommGroup Y] [LinearOrder Y] [AddRightMono Y] [AddLeftMono Y]

instance [AddGroup Y] [LinearOrder Y] [AddLeftMono Y] :
    AddLeftMono (locallyFinsuppWithin U Y) where
  elim a n₁ n₂ h₁ h₂ := by simp [h₁ h₂]

instance [AddGroup Y] [LinearOrder Y] [AddRightMono Y] :
    AddRightMono (locallyFinsuppWithin U Y) where
  elim a n₁ n₂ h₁ h₂ := by simp [h₁ h₂]

/--
The negative part of a minimum is the maximum of the negative parts.
-/
theorem negPart_min' (a b : locallyFinsuppWithin U Y) :
    (min a b)⁻ = max a⁻ b⁻ := by
  apply negPart_min

/--
The negative part of a maximum is the minimum of the negative parts.
-/
theorem negPart_max' (a b : locallyFinsuppWithin U Y) :
    (max a b)⁻ = min a⁻ b⁻ := by
  ext x
  apply negPart_max


end MeromorphicAt
