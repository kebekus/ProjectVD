/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger, Aristotle AI
-/
import Mathlib

/-!
# Differential Operators

-/
open Filter Function Gradient InnerProductSpace Laplacian MeromorphicOn Metric Real Set Classical Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

variable (𝕜 E F G) in
/--
Differential operator of order 0: scalar multiplication of functions
-/
structure DiffOp0 where
  toFun : (E → F) →ₗ[𝕜] (E → G)

  localness (f g x) (h : f =ᶠ[𝓝 x] g) : toFun f x = toFun g x

  leibniz0 (f : E → 𝕜) (g) : toFun (f • g) - f • toFun g = 0

variable (𝕜 E F G) in
/--
Differential operator of order ≤ 1

Note that impose linearity and linearity only for continuously differentiable
functions. Otherwise, Lie derivatives would not be differential operators!
-/
structure DiffOp1 where
  toFun : (E → F) → (E → G)

  map_add' (f₁ f₂ : E → F) (e : E) (hf₁ : ContDiffAt 𝕜 1 f₁ e) (hf₂ : ContDiffAt 𝕜 1 f₂ e) :
    toFun (f₁ + f₂) e = toFun f₁ e + toFun f₂ e

  -- The assumption `hf` is probably not needed.
  map_smul' (f : E → F) (e : E) (m : 𝕜) (hf : ContDiffAt 𝕜 1 f e) :
    toFun (m • f) e = m • toFun f e

  localness (f g x) (h : f =ᶠ[𝓝 x] g) :
    toFun f x = toFun g x

  leibniz1 (φ : E → 𝕜) (e : E) (hφ : ContDiffAt 𝕜 1 φ e) : ∃ D : DiffOp0 𝕜 E F G,
    ∀ g, ContDiffAt 𝕜 1 g e → toFun (φ • g) e - (φ • toFun g) e = D.toFun g e

variable (𝕜 E F G) in
structure DiffOp2 where
  toFun : (E → F) → (E → G)

  map_add' (f₁ f₂ : E → F) (e : E) (hf₁ : ContDiffAt 𝕜 2 f₁ e) (hf₂ : ContDiffAt 𝕜 2 f₂ e) :
    toFun (f₁ + f₂) e = toFun f₁ e + toFun f₂ e

  map_smul' (f : E → F) (e : E) (m : 𝕜) (hf : ContDiffAt 𝕜 2 f e) :
    toFun (m • f) e = m • toFun f e

  localness (f₁ f₂ x) (h : f₁ =ᶠ[𝓝 x] f₂) : toFun f₁ x = toFun f₂ x

  leibniz2 (φ : E → 𝕜) (e : E) (hφ : ContDiffAt 𝕜 1 φ e) : ∃ D : DiffOp1 𝕜 E F G,
    ∀ g, ContDiffAt 𝕜 1 g e → toFun (φ • g) e - (φ • toFun g) e = D.toFun g e

/-!
## Examples: Differential Operator Order 0
-/

/--
Scalar multiplication with a function
-/
noncomputable def scalarMul (φ : E → 𝕜) : DiffOp0 𝕜 E F F where
  toFun := {
    toFun := (φ • ·)
    map_add' := by simp
    map_smul' := by
      intro m g
      ext e
      simp only [Pi.smul_apply', Pi.smul_apply, RingHom.id_apply]
      grind [smul_comm]
  }
  localness (f g x h) := by
    simp [h.eq_of_nhds]
  leibniz0 (f g) := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    grind [smul_comm]

noncomputable def scalarMul₂ (φ : E → G) : DiffOp0 𝕜 E 𝕜 G where
  toFun := {
    toFun := (· • φ)
    map_add' (f₁ f₂) := by
      rw [add_smul]
    map_smul' (m g) := by
      simp
  }
  localness (f g x h) := by
    simp [h.eq_of_nhds]
  leibniz0 (f g) := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    grind [smul_assoc]

/-!
## Examples: Differential Operators of Order ≤ 1
-/

/--
Lie derivative with respect to a vector field
-/
noncomputable def lieDerivative (v : E → E) : DiffOp1 𝕜 E F F where
  toFun (f) := fun e ↦ fderiv 𝕜 f e (v e)
  map_add' (f₁ f₂ e hf₁ hf₂) := by
    simp [fderiv_add (hf₁.differentiableAt one_ne_zero) (hf₂.differentiableAt one_ne_zero)]
  map_smul' (f₁ f₂ m hf) := by
    simp [fderiv_const_smul (hf.differentiableAt one_ne_zero)]
  localness (f g x h) := by
    simp [h.fderiv_eq]
  leibniz1 (φ e hφ) := by
    use scalarMul (fun e ↦ (fderiv 𝕜 φ e) (v e))
    intro g hg
    simp [scalarMul]
    rw [fderiv_smul (hφ.differentiableAt one_ne_zero) (hg.differentiableAt one_ne_zero)]
    simp

/--
Gradient
-/
noncomputable def gradientDiffOp : DiffOp1 ℝ H ℝ H where
  toFun := ∇
  map_add' (f₁ f₂ e hf₁ hf₂) := by
    simp [gradient, fderiv_add (hf₁.differentiableAt one_ne_zero) (hf₂.differentiableAt one_ne_zero)]
  map_smul' (f₁ f₂ m hf) := by
    simp [gradient, fderiv_const_smul (hf.differentiableAt one_ne_zero)]
  localness (f g x h) := by
    simp [gradient, h.fderiv_eq]
  leibniz1 (φ e hφ) := by
    use scalarMul₂ (fun e ↦ (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ φ e))
    intro g hg
    unfold gradient
    rw [fderiv_smul (hφ.differentiableAt one_ne_zero) (hg.differentiableAt one_ne_zero)]
    simp [scalarMul₂]
    have : (fderiv ℝ φ e).smulRight (g e) = (g e) • (fderiv ℝ φ e) := by
      ext x
      rw [ContinuousLinearMap.smulRight_apply]
      simp
      rw [mul_comm]
    rw [this]
    simp

/--
Exterior derivative
-/
noncomputable def extDerivative [FiniteDimensional 𝕜 E] : DiffOp1 𝕜 E 𝕜 (Module.Dual 𝕜 E) where
  toFun (f) := by
    -- choose Basis
    have B := Module.finBasisOfFinrankEq 𝕜 E (rfl)
    exact fun e ↦ ∑ ι, (fderiv 𝕜 f e (B ι)) • (B.dualBasis ι)
  map_add' (f₁ f₂ e hf₁ hf₂) := by
    simp [fderiv_add (hf₁.differentiableAt one_ne_zero) (hf₂.differentiableAt one_ne_zero)]
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' (f₁ e m hf) := by
    simp
    rw [fderiv_const_smul (hf.differentiableAt one_ne_zero), Finset.smul_sum]
    congr
    ext ι
    rw [ContinuousLinearMap.smul_apply, smul_assoc]
  localness (f g x h) := by
    simp [h.fderiv_eq]
  leibniz1 (φ e hφ) := by
    let B := Module.finBasisOfFinrankEq 𝕜 E (rfl)
    use scalarMul₂ (fun e ↦ ∑ x, ((fderiv 𝕜 φ e) (B x)) • B.dualBasis x)
    intro g hg
    simp only [Pi.smul_apply']
    rw [fderiv_smul (hφ.differentiableAt one_ne_zero) (hg.differentiableAt one_ne_zero)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib]
    simp_rw [← ContinuousLinearMap.smul_apply]
    have : ∑ x, (φ e • fderiv 𝕜 g e) (B x) • B.dualBasis x =
        φ e • ∑ ι, (fderiv 𝕜 g e) (B ι) • B.dualBasis ι := by
      rw [Finset.smul_sum]
      congr
      ext ι x
      simp
      ring
    rw [this]
    clear this
    unfold B
    abel_nf
    simp [scalarMul₂]
    rw [Finset.smul_sum]
    congr
    ext ι x
    simp
    ring

/-!
## Examples: Differential Operators of Order ≤ 2
-/

/--
Laplacian
-/
noncomputable def laplacianDiffOp : DiffOp2 ℝ H ℝ ℝ where
  toFun := Δ
  map_add' (f₁ f₂ e hf₁ hf₂) := by
    apply hf₁.laplacian_add hf₂
  map_smul' (f e m hf) := by
    apply laplacian_smul
    exact hf
  localness (f g x h) :=
    (laplacian_congr_nhds h).eq_of_nhds
  leibniz2 (φ e hφ) := by
    have D : DiffOp1 ℝ H ℝ ℝ := by sorry
    use D
    intro g hg
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply]
    have := fderiv_smul (hφ.differentiableAt one_ne_zero) (hg.differentiableAt one_ne_zero)
    rw [this]
    rw [fderiv_smul (hφ.differentiableAt one_ne_zero) (hg.differentiableAt one_ne_zero)]
    simp [scalarMul₂]
    have : (fderiv ℝ φ e).smulRight (g e) = (g e) • (fderiv ℝ φ e) := by
      ext x
      rw [ContinuousLinearMap.smulRight_apply]
      simp
      rw [mul_comm]
    rw [this]
    simp
