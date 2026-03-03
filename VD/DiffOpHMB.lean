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
  {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
set_option linter.unusedVariables false

variable (𝕜 E F G) in
/--
Differential operator of order ≤ n
-/
def DiffOp (n : ℕ) : Type _ := E → (∀ i : Fin (n + 1), E [×i]→L[𝕜] F) → G

noncomputable def diffOp_apply {n : ℕ} (D : DiffOp 𝕜 E F G n) (f : E → F) :
    E → G := fun e ↦ D e ((ftaylorSeries 𝕜 f e) ·)

noncomputable def diffOp_compose {n₁ n₂ : ℕ} (D₁ : DiffOp 𝕜 E G₂ G₁ n₁) (D₂ : DiffOp 𝕜 E F G₂ n₂) :
    DiffOp 𝕜 E F G₁ (n₁ + n₂) := by
  sorry

theorem diffOp_compse_apply {n₁ n₂ : ℕ}
    (D₁ : DiffOp 𝕜 E G₂ G₁ n₁) (D₂ : DiffOp 𝕜 E F G₂ n₂) :
    diffOp_apply (diffOp_compose D₁ D₂) = (diffOp_apply D₁) ∘ (diffOp_apply D₂) := by
  ext f : 1
  unfold diffOp_apply
  simp
  sorry


/-!
## Examples: Differential Operator Order 1
-/

/--
Lie derivative with respect to a vector field
-/
noncomputable def lieDerivative (v : E → E) : DiffOp 𝕜 E F F 1 :=
  fun e fps ↦ fps 1 ![v e]

lemma lieDerivative_apply (f : E → F) (v : E → E) :
    diffOp_apply (lieDerivative (𝕜 := 𝕜) (F := F) v) = (fun f e ↦ fderiv 𝕜 f e (v e)) := by
  ext f e
  simp [diffOp_apply, lieDerivative, ftaylorSeries]
  erw [iteratedFDeriv_one_apply ![v e] (𝕜 := 𝕜) (f := f) (x := e)]
  simp

noncomputable def lieDerivative₂ (v₁ : E → E) (v₂ : E → E) : DiffOp 𝕜 E F F 2 :=
  fun e fps ↦ (fps 1).curryRight.curry0 ((fderiv 𝕜 v₂ e) (v₁ e)) + fps 2 ![v₁ e, v₂ e]

lemma lieDerivative_apply_apply {f : E → F} (v₁ v₂ : E → E) (hf : ContDiff 𝕜 (2 : ℕ) f)
    (ρ₂ : Differentiable 𝕜 v₂) :
    ((diffOp_apply (lieDerivative (𝕜 := 𝕜) (F := F) v₁)) ∘ (diffOp_apply (lieDerivative (𝕜 := 𝕜) (F := F) v₂))) f
      = diffOp_apply (lieDerivative₂ (𝕜 := 𝕜) (F := F) (v₁ : E → E) (v₂ : E → E)) f := by
  simp
  rw [lieDerivative_apply]
  simp
  rw [lieDerivative_apply]
  simp
  ext e
  have ρ₁ : DifferentiableAt 𝕜 (fderiv 𝕜 f) e := by
    apply Differentiable.differentiableAt
    have A := ContDiff.differentiable_iteratedFDeriv (𝕜 := 𝕜) (n := 2) (f := f) (m := 1)
      (by exact compare_gt_iff_gt.mp rfl) hf
    have : iteratedFDeriv 𝕜 1 f = (continuousMultilinearCurryFin1 𝕜 E F).symm ∘ (fderiv 𝕜 f) := by
      ext a b
      simp
    have : (continuousMultilinearCurryFin1 𝕜 E F) ∘ iteratedFDeriv 𝕜 1 f = (fderiv 𝕜 f) := by
      ext a b
      simp
      rfl
    rw [← this]
    apply Differentiable.comp
    fun_prop
    exact A
  have := fderiv_clm_apply (c := fun e ↦ fderiv 𝕜 f e) (u := fun e ↦ v₂ e) (x := e) ρ₁ (ρ₂ e)
  simp at this
  rw [this]
  simp
  have : ((fderiv 𝕜 (fderiv 𝕜 f) e) (v₁ e)) (v₂ e) = iteratedFDeriv 𝕜 2 f e ![v₁ e, v₂ e] := by
    rw [iteratedFDeriv_two_apply]
    rfl
  rw [this]
  simp [diffOp_apply, lieDerivative₂, ftaylorSeries]
  rfl
  exact 0
  exact 0

variable (H)
/--
Gradient
-/
noncomputable def gradientDiffOp : DiffOp ℝ H ℝ H 1 := by
  exact fun e fps ↦ (toDual ℝ H).symm (fps 1).curryRight.curry0

lemma gradientDiffOp_apply (f : H → ℝ) :
    diffOp_apply (gradientDiffOp H) = ∇ := by
  ext g h
  rw [diffOp_apply, gradientDiffOp, ftaylorSeries]
  unfold gradient
  congr
  ext η
  simp
  congr

/--
Exterior derivative
-/
noncomputable def extDerivativeDiffOp [FiniteDimensional 𝕜 E] :
    DiffOp 𝕜 E 𝕜 (Module.Dual 𝕜 E) 1 := by
  let v := Module.finBasisOfFinrankEq 𝕜 E (rfl)
  exact fun e fps ↦ ∑ i, fps 1 ![v i] • (v.dualBasis i)

lemma extDerivativeOp_apply [FiniteDimensional 𝕜 E] (f : E → 𝕜) :
    diffOp_apply extDerivativeDiffOp f
      = (fun e ↦ ∑ i, ((fderiv 𝕜 f e) ((Module.finBasisOfFinrankEq 𝕜 E (rfl)) i)) • ((Module.finBasisOfFinrankEq 𝕜 E (rfl)).dualBasis i)) := by
  ext e e₁
  simp only [diffOp_apply, extDerivativeDiffOp, ftaylorSeries]
  have {e₀ : E} : (iteratedFDeriv 𝕜 1 f e) ![e₀] = fderiv 𝕜 f e e₀ := by
    simp only [iteratedFDeriv_one_apply, Fin.isValue, Matrix.cons_val_fin_one]
  conv =>
    left
    arg 1
    arg 2
    intro i
    simp
    arg 1
    erw [this]
  simp

/-!
## Examples: Differential Operators of Order ≤ 2
-/

noncomputable def laplaceDiffOp : DiffOp ℝ H ℝ ℝ 2 := by
  let v := stdOrthonormalBasis ℝ H
  exact fun e fps ↦ ∑ i, fps 2 ![v i, v i]

lemma laplaceDiffOp_apply [FiniteDimensional 𝕜 E] (f : E → 𝕜) :
    diffOp_apply (laplaceDiffOp H) = Δ := by
  let v := stdOrthonormalBasis ℝ H
  ext g e
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [diffOp_apply, laplaceDiffOp, ftaylorSeries]
  rfl

-- DIV CURL DEL DELBAR
