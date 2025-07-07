/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.Conformal

open Complex

/--
Helper lemma for `differentiableAt_complex_iff_differentiableAt_real`: A real
linear map `ℓ : ℂ →ₗ[ℝ] ℂ` respects complex scalar multiplication if it maps `I`
to `I • ℓ 1`.
-/
theorem real_linearMap_map_smul_complex {ℓ : ℂ →ₗ[ℝ] ℂ} (h : ℓ I = I • ℓ 1) :
    ∀ (a b : ℂ), ℓ (a • b) = a • ℓ b := by
  intro a b
  rw [(by simp only [real_smul, re_add_im] : a = a.re + a.im • I), (by simp : b = b.re + b.im • I)]
  repeat rw [add_smul]
  repeat rw [smul_add]
  repeat rw [ℓ.map_add]
  repeat rw [coe_smul]
  repeat rw [ℓ.map_smul]
  have t₀ : (a.im • I) • ↑b.re = (a.im * b.re) • I := by
    simp
    ring
  have t₁ : (a.im • I) • b.im • I = -(a.im * b.im) • (1 : ℂ) := by
    simp [(by ring : ↑a.im * I * (↑b.im * I) = (↑a.im * ↑b.im) * (I * I))]
  rw [t₀, t₁, (by simp : b.re = b.re • (1 : ℂ))]
  repeat rw [ℓ.map_smul]
  repeat rw [h]
  repeat rw [← coe_smul]
  repeat rw [smul_eq_mul]
  simp only [ofReal_mul, ofReal_neg, neg_mul]
  ring_nf
  simp only [I_sq, mul_neg, mul_one, neg_mul]
  abel_nf

/--
The Cauchy-Riemann Equation: A real-differentiable function `f : ℂ → ℂ` is
complex differentiable if the derivative `fderiv ℝ f x` maps `I` to I • (fderiv
ℝ f x) 1`.
-/
theorem differentiableAt_complex_iff_differentiableAt_real {f : ℂ → ℂ} :
    (DifferentiableAt ℂ f x) ↔ (DifferentiableAt ℝ f x) ∧
      (fderiv ℝ f x I = I • fderiv ℝ f x 1) := by
  constructor
  · exact fun h ↦ by simp [h.restrictScalars ℝ, h.fderiv_restrictScalars ℝ]
  · intro ⟨h₁, h₂⟩
    apply (differentiableAt_iff_restrictScalars ℝ h₁).2
    use {
      toFun := fderiv ℝ f x
      map_add' := (fderiv ℝ f x).map_add'
      map_smul' := real_linearMap_map_smul_complex h₂
    }
    rfl
