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

theorem xx {F : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) :
    AnalyticOn ℂ F s ↔ AnalyticOnNhd ℂ F s := by
  constructor
  · intro h
    exact (IsOpen.analyticOn_iff_analyticOnNhd hs).mp h
  · exact AnalyticOnNhd.analyticOn

theorem harmonic_is_realOfHolomorphic {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : HarmonicOnNhd f (Metric.ball z R)) :
    ∃ F, (AnalyticOnNhd ℂ F (Metric.ball z R)) ∧ (Set.EqOn (Complex.reCLM ∘ F) f (Metric.ball z R)) := by

  let g := ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)
  let F := ((primitive z g) · + f z)

  use F
  constructor
  · apply (IsOpen.analyticOn_iff_analyticOnNhd Metric.isOpen_ball).1
    apply DifferentiableOn.analyticOn
    unfold F
    apply DifferentiableOn.add
    · apply primitive_differentiableOn
      unfold g
      intro y hy

      have := hf.1
      fun_prop

    · sorry

intro x hx

    apply analyticOn_analyticOnNhd
    apply DifferentiableOn.analyticOn
    apply primitive_differentiableOn
    simp

    sorry
  · sorry
