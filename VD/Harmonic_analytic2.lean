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
  have hg : DifferentiableOn ℂ g (Metric.ball z R) := by
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply HarmonicAt.differentiableAt_complex_partial (hf x hx)
  use ((primitive z g) · + f z)
  constructor
  · apply Metric.isOpen_ball.analyticOn_iff_analyticOnNhd.1
    apply ((primitive_differentiableOn hg).add (by fun_prop)).analyticOn Metric.isOpen_ball
  · apply (convex_ball z R).eqOn_of_fderivWithin_eq (𝕜 := ℝ) (x := z)
    · apply DifferentiableOn.comp (t := Set.univ) reCLM.differentiable.differentiableOn
        (((primitive_differentiableOn hg).restrictScalars (𝕜 := ℝ)).add (by fun_prop))
        (by tauto)
    · exact fun x hx ↦ ((hf x hx).1.differentiableAt one_le_two).differentiableWithinAt
    · exact Metric.isOpen_ball.uniqueDiffOn
    · intro x hx
      rw [fderivWithin_eq_fderiv, fderivWithin_eq_fderiv, fderiv_comp]
      simp only [ContinuousLinearMap.fderiv, fderiv_add_const]
      rw [DifferentiableAt.fderiv_restrictScalars (𝕜 := ℝ) (𝕜' := ℂ), primitive_fderiv _ x hx]
      unfold g
      ext y
      simp only [Pi.sub_apply, Function.comp_apply, ofRealCLM_apply, Pi.smul_apply, smul_eq_mul,
        map_sub, ContinuousLinearMap.restrictScalars_sub, ContinuousLinearMap.comp_sub,
        ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_comp',
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.lsmul_apply, reCLM_apply, mul_re, ofReal_re, ofReal_im, mul_zero,
        sub_zero, I_re, zero_mul, I_im, sub_self, mul_im, one_mul, zero_add, zero_sub,
        sub_neg_eq_add]
      nth_rw 3 [(by simp : y = y.re + y.im * Complex.I)]
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
