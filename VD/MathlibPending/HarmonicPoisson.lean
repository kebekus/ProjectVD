/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger, Aristotle AI
-/
--module

import Mathlib.Analysis.Complex.Poisson
import VD.MathlibSubmitted.HarmonicMeanvalue

/-!
# Poisson Integral Formula

This file establishes several versions of the **Poisson Integral Formula** for
harmonic functions on arbitrary disks in the complex plane, formulated with the
real part of the Herglotz–Riesz kernel of integration and with the Poisson
kernel, respectively.
-/

open Complex InnerProductSpace Metric Real Topology

variable
  {f : ℂ → ℝ} {c w : ℂ} {R : ℝ}

private lemma continuousOn_herglotz_riesz (_ : w ∈ ball c R) :
    ContinuousOn (fun x ↦ ((x - c + (w - c)) / (x - c - (w - c))).re) {z | ‖z - c‖ ∈ Set.Ioc ‖w - c‖ R} := by
  have : ∀ x ∈ {z | ‖z - c‖ ∈ Set.Ioc ‖w - c‖ R}, x - c - (w - c) ≠ 0 := by
    grind [mem_ball, mem_sphere]
  fun_prop (disch := assumption)

set_option backward.isDefEq.respectTransparency false in
/--
**Poisson integral formula** for harmonic functions on arbitrary disks in the
complex plane, formulated with the real part of the Herglotz–Riesz kernel of
integration.
-/
theorem HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
    (hf : HarmonicOnNhd f (closedBall c R)) (hw : w ∈ ball c R) :
    Real.circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R = f w := by
  by_cases hR : R ≤ 0
  · simp_all [ball_eq_empty.2 hR]
  rw [not_le] at hR
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c R).exists_thickening_subset_open
    (isOpen_setOf_harmonicAt f) (by aesop)
  rw [thickening_closedBall h₁e hR.le] at h₂e
  obtain ⟨F, h₁F, h₂F⟩ := harmonic_is_realOfHolomorphic h₂e
  have h₃F : DifferentiableOn ℂ F (closure (ball c R)) := by
    intro x hx
    apply (h₁F x _).differentiableWithinAt
    grind [mem_ball, mem_closedBall.1 (closure_ball_subset_closedBall hx)]
  have h₄F : Set.EqOn
      (re ∘ herglotzRieszKernel c w • f)
      (Complex.reCLM ∘ (fun z ↦ ((z - c + (w - c)) / (z - c - (w - c))).re • F z))
      (sphere c R) := by
    intro x hx
    simp [h₂F (sphere_subset_ball (lt_add_of_pos_left R h₁e) hx)]
    left
    simp [herglotzRieszKernel]
  rw [← abs_of_pos hR] at h₄F
  rw [circleAverage_congr_sphere h₄F, reCLM.circleAverage_comp_comm,
    h₃F.diffContOnCl.circleAverage_re_herglotzRieszKernel_smul' hw]
  apply h₂F
  grind [mem_ball]
  -- CircleIntegrable (fun z ↦ ((z - c + (w - c)) / (z - c - (w - c))).re • F z) c R
  apply ContinuousOn.circleIntegrable'
  apply ContinuousOn.smul
  · apply (continuousOn_herglotz_riesz hw).mono
    grind [mem_ball, dist_eq_norm, mem_sphere_iff_norm]
  · apply AnalyticOnNhd.continuousOn (𝕜 := ℂ)
    apply h₁F.mono
    grind [mem_sphere, mem_ball]

set_option backward.isDefEq.respectTransparency false in
/--
**Poisson integral formula** for harmonic functions on arbitrary disks in the
complex plane, formulated with the real part of the Herglotz–Riesz kernel of
integration.
-/
theorem HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
    (hf : HarmonicContOnCl f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R = f w := by
  by_cases hR : R ≤ 0
  · simp_all [ball_eq_empty.2 hR]
  rw [not_le] at hR
  apply ContinuousOn.eq_of_eqOn_Ioo (r := ‖w - c‖)
  · -- ContinuousOn (circleAverage (fun z ↦ ((z - c + (w - c)) / (z - c - (w - c))).re • f z) c) (Set.Ioc ‖w - c‖ R)
    apply ContinuousOn.circleAverage
    · apply (continuousOn_herglotz_riesz hw).smul
      apply hf.2.mono
      grind [closure_ball c hR.ne', mem_closedBall_iff_norm]
    · -- ∀ (r : ↑(Set.Ioc ‖w - c‖ R)), 0 ≤ ↑r
      simp only [Subtype.forall, Set.mem_Ioc, and_imp]
      grind [norm_nonneg (w - c)]
  · grind [mem_ball_iff_norm]
  · intro r hr
    rw [HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul (hf.1.mono (closedBall_subset_ball hr.2))
      (by grind [mem_ball_iff_norm])]

set_option backward.isDefEq.respectTransparency false in
/--
**Poisson integral formula** for harmonic functions on arbitrary disks in the
complex plane, formulated with the Poisson kernel of integration.
-/
theorem HarmonicOnNhd.circleAverage_poissonKernel_smul
    (hf : HarmonicOnNhd f (closedBall c R)) (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w • f) c R = f w := by
  rw [← HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul hf hw]
  apply circleAverage_congr_sphere
  intro z hz
  simp_rw [← poissonKernel_eq_re_herglotzRieszKernel]

set_option backward.isDefEq.respectTransparency false in
/--
**Poisson integral formula** for harmonic functions on arbitrary disks in the
complex plane, formulated with the Poisson kernel of integration.
-/
theorem HarmonicContOnCl.circleAverage_poissonKernel_smul
    (hf : HarmonicContOnCl f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w • f) c R = f w := by
  rw [← HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul hf hw]
  apply circleAverage_congr_sphere
  intro z hz
  simp_rw [← poissonKernel_eq_re_herglotzRieszKernel]
