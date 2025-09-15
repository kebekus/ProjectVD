/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.InnerProductSpace.Harmonic.Analytic
import Mathlib.Analysis.Complex.HasPrimitives

open Complex InnerProductSpace Metric

variable
  {f : ℂ → ℝ} {x : ℂ}

/-
If a function `f : ℂ → ℝ' is harmonic on an open ball, then `f` is the real part
of a function `F : ℂ → ℂ` that is holomorphic on the ball.
-/
theorem harmonic_is_realOfHolomorphic {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : HarmonicOnNhd f (ball z R)) :
    ∃ F, (AnalyticOnNhd ℂ F (ball z R)) ∧ ((ball z R).EqOn (Complex.reCLM ∘ F) f) := by
  let g := ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)
  have hg : DifferentiableOn ℂ g (ball z R) := by
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    exact HarmonicAt.differentiableAt_complex_partial (hf x hx)
  obtain ⟨F₀, hF₀⟩ := hg.isExactOn_ball
  let F := fun x ↦ F₀ x - F₀ z + f z
  have h₁F : ∀ z₁ ∈ ball z R, HasDerivAt F (g z₁) z₁ := by
    simp_all [F]
  have h₂F : DifferentiableOn ℂ F (ball z R) :=
    fun x hx ↦ (h₁F x hx).differentiableAt.differentiableWithinAt
  have h₃F : DifferentiableOn ℝ F (ball z R) :=
    h₂F.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
  use F, h₂F.analyticOnNhd isOpen_ball
  intro x hx
  apply (convex_ball z R).eqOn_of_fderivWithin_eq (𝕜 := ℝ) (x := z)
  · apply reCLM.differentiable.differentiableOn.comp (t := Set.univ) h₃F
    tauto
  · intro y hy
    apply DifferentiableAt.differentiableWithinAt
    apply ContDiffAt.differentiableAt (hf y hy).1 one_le_two
  · exact isOpen_ball.uniqueDiffOn
  · intro y hy
    have h₄F := (h₁F y hy).differentiableAt
    have h₅F := h₄F.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
    rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hy) (reCLM.differentiableAt.comp y h₅F)]
    rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hy) ((hf y hy).1.differentiableAt one_le_two)]
    rw [fderiv_comp y (by fun_prop) h₅F]
    rw [ContinuousLinearMap.fderiv]
    rw [h₄F.fderiv_restrictScalars (𝕜 := ℝ)]
    ext a
    nth_rw 2 [(by simp : a = a.re • (1 : ℂ) + a.im • (I : ℂ))]
    rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]
    simp [HasDerivAt.deriv (h₁F y hy), g]
  · simp [hR]
  · simp [F]
  · assumption
