/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger, Aristotle AI
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import VD.LinearDiffOp.Basic

/-!
# Lie Derivatives as Linear Differential Operators

This file defines the Lie derivative of a function along a vector field as a linear differential
operator of order at most one, together with the associated Lie bracket of vector fields.

## Main definitions

- `lieDerivative`: the Lie derivative of a function along a vector field, as a `LinearDiffOp`.
- `lieBracket`: the Lie bracket of two vector fields, agreeing with `VectorField.lieBracket ℝ`.

## Main results

- `lieBracket_apply`: the commutator of two Lie derivatives is the Lie derivative along the Lie
  bracket.
-/

open Filter Function Metric Real Set Topology

set_option backward.isDefEq.respectTransparency false

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : Set E} {e : E} {n m : ℕ} {f f₁ f₂ : E → F}

noncomputable section

variable (F) in
/--
The Lie derivative along a vector field `v`, as a linear differential operator of order at most
one: `lieDerivative F v` maps a function `f : E → F` to the function `fun e ↦ fderiv ℝ f e (v e)`.
See `lieDerivative_apply`.
-/
def lieDerivative (v : E → E) : LinearDiffOp ℝ E F F 1 where
  tensorField e := {
    toFun fps := fps 1 ![v e]
    map_add' fps₁ fps₂ := rfl
    map_smul' m fps := rfl
    cont := by fun_prop
  }

/--
Applying the Lie derivative along `v` to a function `f` contracts the derivative `fderiv ℝ f`
with the vector field.
-/
lemma lieDerivative_apply (f : E → F) (v : E → E) :
    lieDerivative F v f = (fun e ↦ fderiv ℝ f e (v e)) := by
  simp [linearDiffOp_apply, lieDerivative, ftaylorSeries]

/--
The Lie bracket of two vector fields `v₁` and `v₂`, defined as the difference of the mutual Lie
derivatives. It agrees pointwise with `VectorField.lieBracket ℝ v₁ v₂`.
-/
def lieBracket (v₁ v₂ : E → E) : E → E := lieDerivative E v₁ v₂ - lieDerivative E v₂ v₁

/--
The Lie bracket of vector fields is antisymmetric.
-/
lemma lieBracket_anticomm (v₁ v₂ : E → E) :
    lieBracket v₁ v₂ = - lieBracket v₂ v₁ := by
  unfold lieBracket
  simp [linearDiffOp_apply, lieDerivative, ftaylorSeries]

/--
The commutator of the Lie derivatives along two vector fields is the Lie derivative along their
Lie bracket. The function `f` needs to be `C²` at the point so that Schwarz's theorem applies;
without this hypothesis the second-derivative terms need not cancel and the statement is false.
-/
lemma lieBracket_apply {v₁ v₂ : E → E} (hf : ContDiffAt ℝ 2 f e)
    (hv₁ : DifferentiableAt ℝ v₁ e) (hv₂ : DifferentiableAt ℝ v₂ e) :
    lieDerivative F v₁ (lieDerivative F v₂ f) e - lieDerivative F v₂ (lieDerivative F v₁ f) e
      = lieDerivative F (lieBracket v₁ v₂) f e := by
  have hc : DifferentiableAt ℝ (fderiv ℝ f) e :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  simp only [lieDerivative_apply, lieBracket, Pi.sub_apply]
  rw [fderiv_clm_apply hc hv₂, fderiv_clm_apply hc hv₁]
  simp only [add_apply, ContinuousLinearMap.coe_comp, comp_apply,
    ContinuousLinearMap.flip_apply, map_sub,
    ContDiffAt.isSymmSndFDerivAt hf (by simp) (v₁ e) (v₂ e)]
  abel
