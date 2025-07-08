/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.Conformal

open Complex

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/--
Helper lemma for `differentiableAt_complex_iff_differentiableAt_real`: A real
linear map `ℓ : ℂ →ₗ[ℝ] ℂ` respects complex scalar multiplication if it maps `I`
to `I • ℓ 1`.
-/
lemma real_linearMap_map_smul_complex {ℓ : ℂ →ₗ[ℝ] E} (h : ℓ I = I • ℓ 1) :
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
  repeat rw [coe_smul, ℓ.map_smul]
  have t₂ {r : ℝ}  : ℓ (r : ℂ) = r • ℓ (1 : ℂ) := by
    rw [← ℓ.map_smul]
    congr
    simp
  repeat rw [t₂]
  repeat rw [h]
  match_scalars
  simp only [coe_algebraMap, mul_one, neg_mul, smul_eq_mul]
  ring_nf
  simp
  ring

/--
The Cauchy-Riemann Equation: A real-differentiable function `f` on `ℂ` is
complex-differentiable within `s` if the derivative `fderivWithin ℝ f s x` maps
`I` to I • (fderivWithin ℝ f s x) 1`.
-/
theorem differentiableWithinAt_complex_iff_differentiableWithinAt_real {f : ℂ → E} {x : ℂ}
    {s : Set ℂ} (hs : UniqueDiffWithinAt ℝ s x) :
    (DifferentiableWithinAt ℂ f s x) ↔ (DifferentiableWithinAt ℝ f s x) ∧
      (fderivWithin ℝ f s x I = I • fderivWithin ℝ f s x 1) := by
  constructor
  · intro h
    refine ⟨h.restrictScalars ℝ, ?_⟩
    simp only [← h.restrictScalars_fderivWithin ℝ hs, ContinuousLinearMap.coe_restrictScalars']
    rw [(by simp : I = I • 1), (fderivWithin ℂ f s x).map_smul]
    simp
  · intro ⟨h₁, h₂⟩
    apply (differentiableWithinAt_iff_restrictScalars ℝ h₁ hs).2
    use {
      toFun := fderivWithin ℝ f s x
      map_add' := (fderivWithin ℝ f s x).map_add'
      map_smul' := real_linearMap_map_smul_complex h₂
    }
    rfl

/--
The Cauchy-Riemann Equation: A real-differentiable function `f` on `ℂ` is
complex-differentiable if the derivative `fderiv ℝ f x` maps `I` to I • (fderiv
ℝ f x) 1`.
-/
theorem differentiableAt_complex_iff_differentiableAt_real {f : ℂ → E} {x : ℂ} :
    (DifferentiableAt ℂ f x) ↔ (DifferentiableAt ℝ f x) ∧
      (fderiv ℝ f x I = I • fderiv ℝ f x 1) := by
  refine ⟨fun h ↦ by simp [h.restrictScalars ℝ, h.fderiv_restrictScalars ℝ], ?_⟩
  intro ⟨h₁, h₂⟩
  apply (differentiableAt_iff_restrictScalars ℝ h₁).2
  use {
    toFun := fderiv ℝ f x
    map_add' := (fderiv ℝ f x).map_add'
    map_smul' := real_linearMap_map_smul_complex h₂
  }
  rfl
