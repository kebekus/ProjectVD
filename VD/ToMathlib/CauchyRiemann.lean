/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.Conformal

open Complex

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem aa {ℓ : ℂ →ₗ[ℝ] E} {a : ℝ} {b : ℂ} :
    ℓ ((a : ℂ) • b) = a • ℓ b := by
  rw [coe_smul, ℓ.map_smul]

theorem bb {ℓ : ℂ →ₗ[ℝ] E} {a : ℝ}  :
    ℓ (a : ℂ) = a • ℓ (1 : ℂ) := by
  rw [← ℓ.map_smul]
  congr
  simp

theorem real_linearMap_map_smul_complex' {ℓ : ℂ →ₗ[ℝ] E} (h : ℓ I = I • ℓ 1) :
    ∀ (a b : ℂ), ℓ (a • b) = a • ℓ b := by
  intro a b
  rw [(by simp  : a = (a.re : ℂ) + (a.im : ℂ) • I), (by simp : b = (b.re : ℂ) + (b.im : ℂ) • I)]
  repeat rw [add_smul]
  repeat rw [smul_add]
  repeat rw [ℓ.map_add]
  have t₀ : ((a.im : ℂ) • I) • (b.re : ℂ) = (↑(a.im * b.re) : ℂ) • I := by
    simp only [smul_eq_mul, ofReal_mul]
    ring
  have t₁ : ((a.im : ℂ) • I) • (b.im : ℂ) • I = (↑(- a.im * b.im) : ℂ) • (1 : ℂ) := by
    simp only [smul_eq_mul, neg_mul, ofReal_neg, ofReal_mul, mul_one]
    ring_nf
    simp
  rw [t₀, t₁]
  repeat rw [aa]
  repeat rw [bb]
  repeat rw [h]
  match_scalars
  simp only [coe_algebraMap, mul_one, neg_mul, smul_eq_mul]
  ring_nf
  simp
  ring

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
