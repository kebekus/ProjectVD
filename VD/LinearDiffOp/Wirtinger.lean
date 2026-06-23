/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import VD.LinearDiffOp.Basic

/-!
# Wirtinger Operators

This file defines the Wirtinger operators `∂/∂z` and `∂/∂z̄` for complex-valued functions on the
complex plane, as linear differential operators of order at most one. In terms of the real
Fréchet derivative, they map a function `f` to `(∂f/∂x ∓ I ∂f/∂y) / 2`, where `∂f/∂x` and
`∂f/∂y` denote the derivatives of `f` in the directions `1` and `I`, respectively.

If `f` is complex-differentiable at a point, then `wirtingerDeriv` computes the complex
derivative there, and `wirtingerDerivBar` vanishes; the latter statement is a form of the
Cauchy–Riemann equations.

Being linear differential operators, the Wirtinger operators inherit the generic API of
`LinearDiffOp`; in particular, they are local and act linearly on sufficiently regular functions.

## Main definitions

- `wirtingerDeriv`: the Wirtinger operator `∂/∂z`, as a `LinearDiffOp`.
- `wirtingerDerivBar`: the Wirtinger operator `∂/∂z̄`, as a `LinearDiffOp`.

## Main results

- `DifferentiableAt.wirtingerDeriv_eq_deriv`: on complex-differentiable functions,
  `wirtingerDeriv` computes the complex derivative.
- `DifferentiableAt.wirtingerDerivBar_eq_zero`: the Cauchy–Riemann equations.
-/

open Complex

noncomputable section

/--
The Wirtinger operator `∂/∂z`, as a linear differential operator of order at most one: it maps a
function `f : ℂ → ℂ` to `(∂f/∂x - I ∂f/∂y) / 2`, where `∂f/∂x` and `∂f/∂y` denote the
derivatives of `f` in the directions `1` and `I`. See `wirtingerDeriv_apply`.
-/
def wirtingerDeriv : LinearDiffOp ℝ ℂ ℂ ℂ 1 where
  tensorField _ := {
    toFun fps := (fps 1 ![1] - I * fps 1 ![I]) / 2
    map_add' fps₁ fps₂ := by
      simp only [Pi.add_apply, add_apply]
      ring
    map_smul' c fps := by
      simp only [Pi.smul_apply, smul_apply, RingHom.id_apply, real_smul]
      ring
    cont := by fun_prop
  }

/--
The Wirtinger operator `∂/∂z̄`, as a linear differential operator of order at most one: it maps a
function `f : ℂ → ℂ` to `(∂f/∂x + I ∂f/∂y) / 2`, where `∂f/∂x` and `∂f/∂y` denote the
derivatives of `f` in the directions `1` and `I`. See `wirtingerDerivBar_apply`.
-/
def wirtingerDerivBar : LinearDiffOp ℝ ℂ ℂ ℂ 1 where
  tensorField _ := {
    toFun fps := (fps 1 ![1] + I * fps 1 ![I]) / 2
    map_add' fps₁ fps₂ := by
      simp only [Pi.add_apply, add_apply]
      ring
    map_smul' c fps := by
      simp only [Pi.smul_apply, smul_apply, RingHom.id_apply, real_smul]
      ring
    cont := by fun_prop
  }

set_option backward.isDefEq.respectTransparency false in
/--
Applying `wirtingerDeriv` to a function `f` yields `(∂f/∂x - I ∂f/∂y) / 2`, expressed in terms
of the real Fréchet derivative of `f`.
-/
lemma wirtingerDeriv_apply (f : ℂ → ℂ) :
    wirtingerDeriv f = fun z ↦ (fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2 := by
  simp [linearDiffOp_apply, wirtingerDeriv, ftaylorSeries]

set_option backward.isDefEq.respectTransparency false in
/--
Applying `wirtingerDerivBar` to a function `f` yields `(∂f/∂x + I ∂f/∂y) / 2`, expressed in
terms of the real Fréchet derivative of `f`.
-/
lemma wirtingerDerivBar_apply (f : ℂ → ℂ) :
    wirtingerDerivBar f = fun z ↦ (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2 := by
  simp [linearDiffOp_apply, wirtingerDerivBar, ftaylorSeries]

variable {f : ℂ → ℂ} {z : ℂ}

/--
On functions that are complex-differentiable at a point, the Wirtinger operator `∂/∂z` computes
the complex derivative.
-/
theorem DifferentiableAt.wirtingerDeriv_eq_deriv (h : DifferentiableAt ℂ f z) :
    wirtingerDeriv f z = deriv f z := by
  simp only [wirtingerDeriv_apply, h.fderiv_restrictScalars (𝕜 := ℝ),
    ContinuousLinearMap.coe_restrictScalars', fderiv_eq_smul_deriv, smul_eq_mul, one_mul,
    ← mul_assoc, I_mul_I]
  ring

/--
**Cauchy–Riemann equations**: the Wirtinger operator `∂/∂z̄` vanishes on functions that are
complex-differentiable at a point.
-/
theorem DifferentiableAt.wirtingerDerivBar_eq_zero (h : DifferentiableAt ℂ f z) :
    wirtingerDerivBar f z = 0 := by
  simp only [wirtingerDerivBar_apply, h.fderiv_restrictScalars (𝕜 := ℝ),
    ContinuousLinearMap.coe_restrictScalars', fderiv_eq_smul_deriv, smul_eq_mul, one_mul,
    ← mul_assoc, I_mul_I]
  ring

end
