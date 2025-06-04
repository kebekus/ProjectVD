/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
import VD.IteratedFDeriv_two

/-!
# The Laplace Operator

This file defines the Laplace operator for functions on real,
finite-dimensional, inner product spaces. It provides supporting API and
establishes the standard formula, computing the Laplace operator from any
orthonormal basis.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : E → F} {x : E}

open InnerProductSpace TensorProduct Topology

/-!
## Definition of the Laplace Operator
-/

variable (f) in
/--
Definition of the Laplace operator for functions on real inner product spaces.
-/
noncomputable def Real.Laplace : E → F :=
  fun x ↦ tensor_of_iteratedFDeriv_two ℝ f x (InnerProductSpace.canonicalCovariantTensor E)

/--
Introduce `Δ` as a notation for the Laplace operator.
-/
notation "Δ" => Real.Laplace

/-!
## Computation in Terms of Orthonormal Bases
-/

variable (f) in
/--
Standard formula, computing the Laplace operator from any orthonormal basis.
-/
theorem laplace_eq_iteratedFDeriv_orthonormalBasis {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℝ E) :
    Δ f = fun x ↦ ∑ i, iteratedFDeriv ℝ 2 f x ![v i, v i] := by
  ext x
  simp [Real.Laplace, canonicalCovariantTensor_eq_sum E v,
    tensor_of_iteratedFDeriv_two_eq_iteratedFDeriv]

variable (f) in
/--
Standard formula, computing the Laplace operator from the standard orthonormal
basis of a real inner product space.
-/
theorem laplace_eq_iteratedFDeriv_stdOrthonormalBasis :
    Δ f = fun x ↦
      ∑ i, iteratedFDeriv ℝ 2 f x ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] :=
  laplace_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)

/--
Special case of the standard formula for functions on `ℂ`, considered as a real
inner product space.
-/
theorem laplace_eq_iteratedFDeriv_complexPlane (f : ℂ → F) :
    Δ f = fun x ↦
      iteratedFDeriv ℝ 2 f x ![1, 1] + iteratedFDeriv ℝ 2 f x ![Complex.I, Complex.I] := by
  simp [laplace_eq_iteratedFDeriv_orthonormalBasis f Complex.orthonormalBasisOneI]

/-!
## Congruence Lemmata
-/

theorem laplace_congr_nhd (h : f₁ =ᶠ[𝓝 x] f₂) :
    Δ f₁ =ᶠ[𝓝 x] Δ f₂ := by
  filter_upwards [Filter.EventuallyEq.iteratedFDeriv ℝ h 2] with x hx
  simp [laplace_eq_iteratedFDeriv_stdOrthonormalBasis, hx]

/-!
## ℂ-Linearity on Continuously Differentiable Functions
-/

theorem ContDiffAt.laplace_add (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) x = (Δ f₁) x + (Δ f₂) x := by
  simp [laplace_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_add_distrib, iteratedFDeriv_add_apply h₁ h₂]

theorem ContDiffAt.laplace_add_nhd (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) =ᶠ[𝓝 x] (Δ f₁) + (Δ f₂):= by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplace_add h₂x

theorem laplace_smul (v : ℝ) (hf : ContDiffAt ℝ 2 f x) : Δ (v • f) x = v • (Δ f) x := by
  simp [laplace_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_smul_apply hf,
    Finset.smul_sum]

/-!
## Commutativity with Linear Operators

This section establishes commutativity with linear operators, showing in
particular that `Δ` commutes with taking real and imaginary parts of
complex-valued functions.
-/

theorem ContDiffAt.laplace_CLM_comp {l : F →L[ℝ] G} (h : ContDiffAt ℝ 2 f x) :
    Δ (l ∘ f) x = (l ∘ (Δ f)) x := by
  simp [laplace_eq_iteratedFDeriv_stdOrthonormalBasis]
  rw [iteratedFDeriv_comp]
  sorry

theorem laplace_CLE_comp {l : F ≃L[ℝ] G} :
    Δ (l ∘ f) = l ∘ (Δ f) := by
  sorry
