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
  {Y : Type*} [AddCommGroup Y] [LinearOrder Y]

@[to_additive]
theorem leOnePart_min {Y : Type*} [CommGroup Y] [LinearOrder Y] [MulLeftMono Y] (a b : Y) :
    (min a b)⁻ᵐ = max a⁻ᵐ b⁻ᵐ := by
  rcases lt_trichotomy a b with h | h | h
  · rw [min_eq_left h.le, max_comm, max_eq_right ((le_iff_oneLePart_leOnePart a b).1 h.le).2]
  · simp_all
  · rw [min_comm, min_eq_left h.le, max_eq_right ((le_iff_oneLePart_leOnePart b a).1 h.le).2]

theorem negPart_min' {α : Type*} [Lattice α] [AddGroup α] [AddLeftMono α] [AddRightMono α] (a b : α) :
    (min a b)⁻ = max a⁻ b⁻ := by
  simp [negPart, neg_inf, sup_sup_distrib_right]

end MeromorphicAt
