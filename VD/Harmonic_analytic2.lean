/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.Harmonic_analytic
import VD.holomorphic_primitive

open Complex InnerProductSpace Topology

variable
  {f : ℂ → ℝ} {x : ℂ}

theorem harmonic_is_realOfHolomorphic {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : HarmonicOnNhd f (Metric.ball z R)) :
    ∃ F, (AnalyticOnNhd ℂ F (Metric.ball z R)) ∧ (Set.EqOn (Complex.reCLM ∘ F) f (Metric.ball z R)) := by
  let g := ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)
  use ((primitive z g) · + f z)
  constructor
  · apply (IsOpen.analyticOn_iff_analyticOnNhd Metric.isOpen_ball).1
    apply DifferentiableOn.analyticOn _ Metric.isOpen_ball
    apply DifferentiableOn.add
    · apply primitive_differentiableOn
      unfold g
      intro y hy
      apply DifferentiableAt.differentiableWithinAt
      exact HarmonicAt.differentiableAt_complex_partial (hf y hy)
    · fun_prop
  · apply Convex.eqOn_of_fderivWithin_eq (𝕜 := ℝ) (x := z)
    · exact (convex_ball z R)
    · apply DifferentiableOn.comp (t := Set.univ)
      · apply Differentiable.differentiableOn
        exact ContinuousLinearMap.differentiable reCLM
      · apply DifferentiableOn.add
        · apply DifferentiableOn.restrictScalars (𝕜' := ℂ) (𝕜 := ℝ)
          apply primitive_differentiableOn
          intro x hx
          apply DifferentiableAt.differentiableWithinAt
          apply HarmonicAt.differentiableAt_complex_partial
          exact hf x hx
        · fun_prop
      · tauto
    · intro x hx
      apply ((hf x hx).1.differentiableAt one_le_two).differentiableWithinAt
    · exact Metric.isOpen_ball.uniqueDiffOn
    · intro x hx
      rw [fderivWithin_eq_fderiv, fderivWithin_eq_fderiv, fderiv_comp]
      simp
      rw [DifferentiableAt.fderiv_restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)]
      rw [primitive_fderiv _ x hx]
      unfold g
      ext y
      simp
      have : y = y.re + y.im * Complex.I := by simp
      nth_rw 3 [this]
      rw [(fderiv ℝ f x).map_add]
      congr 1
      · sorry
      · sorry
      sorry
      sorry
      sorry
      sorry
      sorry
      sorry
      sorry
      sorry
    · exact Metric.mem_ball_self hR
    · simp [primitive_zeroAtBasepoint]
