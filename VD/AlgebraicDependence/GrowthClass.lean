/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Growth Classes — Algebraic Dependence work package D/F2

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §6 (D3) and §8 (F2).

A **growth class** along a filter `l ≤ atTop` is a class of real functions closed under the
operations that the Nevanlinna characteristic produces: constants, sums, and eventual
domination of eventually nonnegative functions. The two standard instances are the big-O class
`(· =O[l] φ)` for a comparison function `φ` dominating the constants, and the little-o class
`(· =o[l] φ)` for `φ → ∞`. The classical class `S(r, f)` of "small functions" with respect to a
nonconstant meromorphic `f` is the little-o class with `φ = T(r, f)` along
`volume.cofinite ⊓ atTop`.

This file has no Nevanlinna-theoretic content; it only fixes the axioms and proves the two
instances. Package D uses it to state the growth-class form of the polynomial Valiron–Mohon'ko
identity; package F builds the growth *fields* of meromorphic germs on top of it.

## Main definitions and results

- `IsGrowthClass l G`: the structure.
- `IsGrowthClass.nsmul`, `IsGrowthClass.sum`: derived closure properties.
- `isGrowthClass_isBigO`, `isGrowthClass_isLittleO`: the two instances.
-/

@[expose] public section

open Asymptotics Filter Finset

/-- A **growth class** along a filter `l ≤ atTop`: a class of real functions closed under
constants, sums, and eventual domination of eventually nonnegative functions. -/
structure IsGrowthClass (l : Filter ℝ) (G : (ℝ → ℝ) → Prop) : Prop where
  /-- Growth classes live along filters finer than `atTop`, so that `1 ≤ r` eventually. -/
  le_atTop : l ≤ atTop
  /-- Constants belong to the class. -/
  const : ∀ c : ℝ, G (fun _ ↦ c)
  /-- The class is closed under sums. -/
  add : ∀ {u v : ℝ → ℝ}, G u → G v → G (u + v)
  /-- An eventually nonnegative function eventually dominated by a member of the class belongs
  to the class. -/
  of_le : ∀ {u v : ℝ → ℝ}, G v → (∀ᶠ r in l, 0 ≤ u r) → (∀ᶠ r in l, u r ≤ v r) → G u

/-- Eventual domination of nonnegative functions, in the language of `IsBigO`: an eventually
nonnegative `u` with `u ≤ v` eventually satisfies `u =O[l] v`. -/
theorem Asymptotics.isBigO_of_eventually_nonneg_of_le {l : Filter ℝ} {u v : ℝ → ℝ}
    (hu : ∀ᶠ r in l, 0 ≤ u r) (huv : ∀ᶠ r in l, u r ≤ v r) : u =O[l] v := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hu, huv] with r hu huv
  rw [one_mul, Real.norm_of_nonneg hu]
  exact huv.trans (le_abs_self _)

namespace IsGrowthClass

variable {l : Filter ℝ} {G : (ℝ → ℝ) → Prop} (hG : IsGrowthClass l G)
include hG

theorem zero : G 0 := hG.const 0

theorem nsmul {u : ℝ → ℝ} (hu : G u) (n : ℕ) : G (n • u) := by
  induction n with
  | zero => simpa using hG.zero
  | succ n ih => rw [succ_nsmul]; exact hG.add ih hu

theorem sum {ι : Type*} {s : Finset ι} {u : ι → ℝ → ℝ} (hu : ∀ i ∈ s, G (u i)) :
    G (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hG.zero
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact hG.add (hu i (mem_insert_self i s)) (ih fun j hj ↦ hu j (mem_insert_of_mem hj))

end IsGrowthClass

/-- The big-O class along `l` with respect to a comparison function dominating the constants
is a growth class. -/
theorem isGrowthClass_isBigO {l : Filter ℝ} (hl : l ≤ atTop) {φ : ℝ → ℝ}
    (hφ : (1 : ℝ → ℝ) =O[l] φ) : IsGrowthClass l (· =O[l] φ) where
  le_atTop := hl
  const c := (isBigO_const_const c one_ne_zero l).trans hφ
  add hu hv := hu.add hv
  of_le hv hu huv := (Asymptotics.isBigO_of_eventually_nonneg_of_le hu huv).trans hv

/-- The little-o class along `l` with respect to a comparison function tending to infinity is
a growth class. -/
theorem isGrowthClass_isLittleO {l : Filter ℝ} (hl : l ≤ atTop) {φ : ℝ → ℝ}
    (hφ : Tendsto φ l atTop) : IsGrowthClass l (· =o[l] φ) where
  le_atTop := hl
  const c := by
    refine isLittleO_const_left.2 (Or.inr ?_)
    simpa [Function.comp_def, Real.norm_eq_abs] using tendsto_abs_atTop_atTop.comp hφ
  add hu hv := hu.add hv
  of_le hv hu huv := (Asymptotics.isBigO_of_eventually_nonneg_of_le hu huv).trans_isLittleO hv
