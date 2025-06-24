/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
### Restricting Scalars in Iterated Derivatives

This file establishes standard theorems on restriction of scalars for iterated
Fréchet derivatives, similar to those found in
`Mathlib.Analysis.Calculus.FDeriv.RestrictScalars`.
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {x : E}

open Topology

theorem fderiv_restrictScalarsLinear_comp {n : ℕ}
    {f : E → (ContinuousMultilinearMap 𝕜' (fun _ : Fin n ↦ E) F)}
    (h : DifferentiableAt 𝕜' f x) :
    (fderiv 𝕜 ((ContinuousMultilinearMap.restrictScalarsLinear 𝕜) ∘ f) x)
      = (ContinuousMultilinearMap.restrictScalars 𝕜) ∘ ((fderiv 𝕜' f x).restrictScalars 𝕜) := by
  rw [fderiv_comp _ (by fun_prop) (h.restrictScalars 𝕜), ContinuousLinearMap.fderiv]
  ext a b
  simp [h.fderiv_restrictScalars 𝕜]

theorem ContDiffAt.differentiableAt_iteratedFDeriv
    {f : E → F} {n : WithTop ℕ∞} {m : ℕ} {x : E} (h : ContDiffAt 𝕜 n f x) (hmn : ↑m < n) :
    DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 m f) x := by
  rw [← differentiableWithinAt_univ]
  convert (h.differentiableWithinAt_iteratedFDerivWithin hmn (by simp [uniqueDiffOn_univ]))
  exact iteratedFDerivWithin_univ.symm

theorem ContDiffAt.iteratedFDeriv_restrictScalars_eventuallyEq {f : E → F} {n : ℕ}
    (h : ContDiffAt 𝕜' n f x) :
    (ContinuousMultilinearMap.restrictScalarsLinear 𝕜) ∘ (iteratedFDeriv 𝕜' n f) =ᶠ[𝓝 x]
      (iteratedFDeriv 𝕜 n f) := by
  induction n with
  | zero =>
    filter_upwards with a
    ext m
    simp [iteratedFDeriv_zero_apply m]
  | succ n hn =>
    have : ContDiffAt 𝕜' n f x := h.of_le (Nat.cast_le.mpr (n.le_add_right 1))
    have t₀ := hn this
    have t₁ := this.eventually
    simp only [ne_eq, ENat.natCast_ne_coe_top, not_false_eq_true, forall_const] at t₁
    filter_upwards [t₀.eventually_nhds, t₁.eventually_nhds,
      h.eventually (by simp)] with a h₁a h₂a h₃a
    rw [← Filter.EventuallyEq] at h₁a
    ext m
    simp only [ContinuousMultilinearMap.restrictScalarsLinear_apply, Function.comp_apply,
      ContinuousMultilinearMap.coe_restrictScalars, iteratedFDeriv_succ_apply_left]
    rw [← h₁a.fderiv_eq, fderiv_restrictScalarsLinear_comp]
    · simp
    · apply h₃a.differentiableAt_iteratedFDeriv
      rw [Nat.cast_lt]
      simp

theorem ContDiffAt.iteratedFDeriv_restrictScalars {f : E → F} {n : ℕ} {z : E}
    (h : ContDiffAt 𝕜' n f z) :
    ((ContinuousMultilinearMap.restrictScalarsLinear 𝕜) ∘ (iteratedFDeriv 𝕜' n f)) z =
      iteratedFDeriv 𝕜 n f z :=
  h.iteratedFDeriv_restrictScalars_eventuallyEq.eq_of_nhds
