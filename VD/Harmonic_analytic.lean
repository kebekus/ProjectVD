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
        rw [(by simp : m = m.re + m.im • I)]
        rw [(by simp : y = y.re + y.im • I)]
        rw [add_smul, smul_add, smul_add, add_smul,
          ContinuousLinearMap.map_add, ContinuousLinearMap.map_add,
          ContinuousLinearMap.map_add, ContinuousLinearMap.map_add,
          smul_add, smul_add]
        congr
        · apply (fderiv ℝ f x).map_smul
        · apply (fderiv ℝ f x).map_smul
        · have : (m.im • I) • ↑y.re = (m.im • y.re) • I := by
            repeat rw [← coe_smul]
            repeat rw [smul_eq_mul]
            rw [ofReal_mul, mul_assoc, mul_assoc]
            congr 1
            rw [mul_comm]
          rw [this]
          rw [ContinuousLinearMap.map_smul, h₂]
          have : ofReal y.re = (y.re) • (1 : ℂ) := by simp
          rw [this]
          rw [ContinuousLinearMap.map_smul]
          rw [← smul_assoc]
          repeat rw [← coe_smul]
          rw [← smul_assoc]
          congr 1
          · rw [smul_eq_mul]
            rw [smul_eq_mul]
            rw [smul_eq_mul]
            rw [smul_eq_mul]
            rw [ofReal_mul]
            ring
        ·
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
