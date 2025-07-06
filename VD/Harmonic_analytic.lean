/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.ToMathlib.Harmonic
import VD.ToMathlib.restrictScalars
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic


open Complex InnerProductSpace Topology

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : ℂ → ℝ} {x : ℂ}

theorem xx {l : ℂ →L[ℝ] ℂ} (h : l I = I • l 1) :
    ∀ (a b : ℂ), l (a • b) = a • l b := by
  intro a b
  rw [(by simp : a = a.re + a.im • I)]
  rw [(by simp : b = b.re + b.im • I)]
  --repeat rw [smul_eq_mul]
  rw [add_smul, add_smul]
  rw [smul_add, smul_add]
  repeat rw [l.map_add]
  repeat rw [coe_smul]
  repeat rw [l.map_smul]


  sorry

theorem CauchyRiemann₇  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {f : ℂ → G} :
    (DifferentiableAt ℂ f x) ↔ (DifferentiableAt ℝ f x) ∧
      (fderiv ℝ f x I = I • fderiv ℝ f x 1) := by
  constructor
  · exact fun h ↦ by simp [h.restrictScalars ℝ, h.fderiv_restrictScalars ℝ]
  · intro ⟨h₁, h₂⟩
    apply (differentiableAt_iff_restrictScalars ℝ h₁).2
    use {
      toFun := fderiv ℝ f x
      map_add' := (fderiv ℝ f x).map_add'
      map_smul' m y := by
        rw [RingHom.id_apply]
        calc (fderiv ℝ f x) (m • y)
        _ = (fderiv ℝ f x) ((m.re * y.re - m.im * y.im) + (m.re * y.im + m.im * y.re) • I) := by
          congr 1
          nth_rw 1 [(by simp : m = m.re + m.im • I)]
          nth_rw 1 [(by simp : y = y.re + y.im • I)]
          rw [add_smul, add_smul]
          rw [smul_add, smul_add]
          simp only [smul_eq_mul, real_smul, ofReal_mul]
          ring_nf
          simp
          ring
        _ = (fderiv ℝ f x) ((m.re * y.re - m.im * y.im) • (1 : ℂ) + (m.re * y.im + m.im * y.re) • I) := by
          simp
        _ = m • (fderiv ℝ f x) y := by
          rw [(fderiv ℝ f x).map_add]
          rw [(fderiv ℝ f x).map_smul]
          rw [(fderiv ℝ f x).map_smul]
          rw [h₂]
          sorry
    }
    rfl


/--
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 + I • ∂f/∂I` is complex
differentiable at `x`.
-/
theorem HarmonicAt.xx (hf : HarmonicAt f x) :
    DifferentiableAt ℂ (ofRealCLM ∘ (fderiv ℝ f · 1) + I • ofRealCLM ∘ (fderiv ℝ f · I)) x := by

  sorry
