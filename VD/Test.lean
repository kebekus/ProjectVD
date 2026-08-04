/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# The Mean Value Property of Vector-Valued Harmonic Functions

The file `Mathlib/Analysis/Complex/Harmonic/MeanValue.lean` establishes the mean value property for
harmonic functions `f : ℂ → ℝ`. Harmonicity is however defined for functions with values in an
arbitrary real normed vector space `F`, and the mean value property holds in that generality, as
soon as `F` is complete. This file proves the generalized statements; they are intended to replace
the real-valued versions in Mathlib.

Completeness of `F` cannot be dropped: `circleAverage` is defined in terms of the Bochner integral,
which is junk (zero) whenever the target space is incomplete.

The proof reduces to the real-valued case. Circle averages commute with continuous linear maps, and
composition with continuous linear maps preserves harmonicity. So `g (circleAverage f c R)` equals
`circleAverage (g ∘ f) c R = g (f c)` for every continuous linear functional `g : F →L[ℝ] ℝ`. Since
continuous linear functionals separate the points of a normed space (Hahn-Banach, in the form of
`SeparatingDual.eq_iff_forall_dual_eq`), this suffices.
-/

open InnerProductSpace Metric Real

namespace InnerProductSpace

/-!
## Compatibility of `HarmonicContOnCl` with Linear Maps
-/

section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/--
Compositions of continuous `ℝ`-linear maps with functions that are harmonic on a set and continuous
on its closure are again harmonic on the set and continuous on its closure.
-/
theorem HarmonicContOnCl.comp_CLM {f : E → F} {s : Set E} (h : HarmonicContOnCl f s)
    (l : F →L[ℝ] G) :
    HarmonicContOnCl (l ∘ f) s :=
  ⟨h.1.comp_CLM l, l.continuous.comp_continuousOn h.2⟩

end

/-!
## The Mean Value Property
-/

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℂ → F} {c : ℂ} {R : ℝ}

/--
The **Mean Value Property** of harmonic functions: If `f : ℂ → F` is harmonic in a neighborhood of a
closed disc of radius `R` and center `c`, then the circle average `circleAverage f c R` equals
`f c`.
-/
theorem HarmonicOnNhd.circleAverage_eq (hf : HarmonicOnNhd f (closedBall c |R|)) :
    circleAverage f c R = f c := by
  have h : CircleIntegrable f c R :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro g
  rw [← g.circleAverage_comp_comm h]
  exact _root_.HarmonicOnNhd.circleAverage_eq (hf.comp_CLM g)

/--
The **Mean Value Property** of harmonic functions: If `f : ℂ → F` is harmonic on a disc of radius
`|R|` and center `c` and continuous on its closure, then the circle average `circleAverage f c R`
equals `f c`.
-/
theorem HarmonicContOnCl.circleAverage_eq (hf : HarmonicContOnCl f (ball c |R|)) :
    circleAverage f c R = f c := by
  have h : CircleIntegrable f c R :=
    (hf.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro g
  rw [← g.circleAverage_comp_comm h]
  exact _root_.HarmonicContOnCl.circleAverage_eq (hf.comp_CLM g)

end InnerProductSpace
