import VD.Harmonic
import VD.ToMathlib.restrictScalars

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : ℂ → F}
  {s t : Set E} {c : ℝ}

open Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem ContDiffAt.harmonicAt  {f : ℂ → F} {x : ℂ} (h : ContDiffAt ℂ 2 f x) :
    HarmonicAt f x := by
  constructor
  · exact ContDiffAt.restrict_scalars ℝ h
  · filter_upwards [h.iteratedFDeriv_restrictScalars_eventuallyEq (𝕜 := ℝ)] with a ha
    simp only [laplace_eq_iteratedFDeriv_complexPlane f, ← ha,
      ContinuousMultilinearMap.restrictScalarsLinear_apply, Function.comp_apply,
      ContinuousMultilinearMap.coe_restrictScalars, Pi.ofNat_apply]
    rw [iteratedFDeriv_two_apply]
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [fderiv_eq_smul_deriv, one_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply]
    sorry
