/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger, Aristotle AI
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.HasPrimitives
import VD.LinearDiffOp.Basic

open Filter Function Metric Real Set Classical Topology

set_option backward.isDefEq.respectTransparency false

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : Set E} {e : E} {n m : ℕ} {f f₁ f₂ : E → F}

noncomputable section

variable (F) in
/--
Lie derivative with respect to a vector field
-/
def lieDerivative (v : E → E) : LinearDiffOp ℝ E F F 1 where
  tensorField e := {
    toFun fps := fps 1 ![v e]
    map_add' fps₁ fps₂ := by apply ContinuousMultilinearMap.add_apply
    map_smul' m fps := by apply ContinuousMultilinearMap.smul_apply
    cont := by fun_prop
  }

/--
Application of the Lie derivative to a function `f` equals contraction the
derivative to `fderiv 𝕜 f` with the vector field.
-/
lemma lieDerivative_apply (f : E → F) (v : E → E) :
    lieDerivative F v f = (fun e ↦ fderiv ℝ f e (v e)) := by
  simp [linearDiffOp_apply, lieDerivative, ftaylorSeries]

def lieBracket (v₁ v₂ : E → E) : E → E := lieDerivative E v₁ v₂ - lieDerivative E v₂ v₁

lemma lieBracket_anticomm (v₁ v₂ : E → E) :
    lieBracket v₁ v₂ = - lieBracket v₂ v₁ := by
  unfold lieBracket
  simp [linearDiffOp_apply, lieDerivative, ftaylorSeries]

lemma lieBracket_apply (v₁ v₂ : E → E) :
    lieDerivative E v₁ ∘ lieDerivative E v₂ - lieDerivative E v₂ ∘ lieDerivative E v₁
      = (lieDerivative E (lieBracket v₁ v₂)) := by
  ext f : 1
  simp [lieDerivative_apply, lieBracket]
  ext e
  simp
  --have := iteratedFDeriv_two_apply
  have := fderiv_clm_apply (c := fun e ↦ fderiv ℝ f e) (u := fun e ↦ v₂ e) (x := e)
  simp at this
  rw [this]
  clear this

  have := fderiv_clm_apply (c := fun e ↦ fderiv ℝ f e) (u := fun e ↦ v₁ e) (x := e)
  simp at this
  rw [this]
  clear this

  simp
  sorry
  sorry
  sorry
  sorry
  sorry


/--
Differential operate ∂/∂z for complex-valued functions on the complex plane.
-/
def del_by_del_z := lieDerivative ℂ (fun _ ↦ (1 - Complex.I) / 2)

/--
Application of the Lie derivative to a function `f` equals contraction the
derivative to `fderiv 𝕜 f` with the vector field.
-/
lemma del_by_del_z_apply (f : ℂ → ℂ) :
    del_by_del_z f = (fun e ↦ fderiv ℝ f e ((1 - Complex.I) / 2)) := by
  simp [linearDiffOp_apply, del_by_del_z, lieDerivative, ftaylorSeries]

/--
Differential operate ∂/∂z for complex-valued functions on the complex plane.
delDelZ
-/
def del_by_del_z_bar := lieDerivative ℂ (fun _ ↦ (1 + Complex.I) / 2)

lemma del_by_del_z_bar_apply (f : ℂ → ℂ) :
    del_by_del_z_bar f = (fun e ↦ fderiv ℝ f e ((1 + Complex.I) / 2)) := by
  simp [linearDiffOp_apply, del_by_del_z_bar, lieDerivative, ftaylorSeries]
