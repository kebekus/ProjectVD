/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.ToMathlib.Harmonic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Complex InnerProductSpace Topology

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : ℂ → ℝ} {x : ℂ}

theorem xx {ℓ : ℂ →L[ℝ] ℂ} (h : ℓ I = I • ℓ 1) :
    ∀ (a b : ℂ), ℓ (a • b) = a • ℓ b := by
  intro a b
  rw [(by simp : a = a.re + a.im • I)]
  rw [(by simp : b = b.re + b.im • I)]
  --repeat rw [smul_eq_mul]
  rw [add_smul, add_smul]
  rw [smul_add, smul_add]
  repeat rw [ℓ.map_add]
  repeat rw [coe_smul]
  repeat rw [ℓ.map_smul]
  have : (a.im • I) • ↑b.re = (a.im * b.re) • I := by
    simp
    ring
  rw [this]
  have : (a.im • I) • b.im • I = -(a.im * b.im) • (1 : ℂ) := by
    have : ↑a.im * I * (↑b.im * I) = (↑a.im * ↑b.im) * (I * I) := by
      ring
    simp [this]
  rw [this]
  have : b.re = b.re • (1 : ℂ) := by
    simp
  rw [this]
  repeat rw [ℓ.map_smul]
  repeat rw [h]
  repeat rw [← coe_smul]
  repeat rw [smul_eq_mul]
  simp
  ring_nf
  simp
  abel_nf

theorem CauchyRiemann₇
    {f : ℂ → ℂ} :
    (DifferentiableAt ℂ f x) ↔ (DifferentiableAt ℝ f x) ∧
      (fderiv ℝ f x I = I • fderiv ℝ f x 1) := by
  constructor
  · exact fun h ↦ by simp [h.restrictScalars ℝ, h.fderiv_restrictScalars ℝ]
  · intro ⟨h₁, h₂⟩
    apply (differentiableAt_iff_restrictScalars ℝ h₁).2
    use {
      toFun := fderiv ℝ f x
      map_add' := (fderiv ℝ f x).map_add'
      map_smul' := xx h₂
    }
    rfl


/--
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 - I • ∂f/∂I` is complex
differentiable at `x`.
-/
theorem HarmonicAt.xx (hf : HarmonicAt f x) :
    DifferentiableAt ℂ (ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)) x := by
  have := hf.1
  apply CauchyRiemann₇.2
  constructor
  · fun_prop
  · repeat rw [fderiv_add]
    repeat rw [fderiv_sub]
    repeat rw [fderiv_const_smul]
    repeat rw [fderiv_comp]
    simp
    repeat rw [mul_add]
    repeat rw [mul_sub]
    ring_nf
    simp
    rw [add_comm]
    rw [sub_eq_add_neg]
    congr 1
    · sorry
    · have := hf.2
      sorry
    simp
    fun_prop
    repeat rw [fderiv_add]
    sorry
    sorry
