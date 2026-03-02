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
set_option linter.unusedVariables false

variable (𝕜 E F G)
/--
Differential operator of order ≤ n
-/
def DiffOp (n : ℕ) : Type _ :=
  E → (∀ i : Fin (n + 1), E [×i]→L[𝕜] F) → G

noncomputable def diffOp_apply {n : ℕ} (D : DiffOp 𝕜 E F G n) (f : E → F) :
    E → G := fun e ↦ D e ((ftaylorSeries 𝕜 f e) ·)

/-!
## Examples: Differential Operator Order 1
-/

/--
Lie derivative with respect to a vector field
-/
noncomputable def lieDerivative (v : E → E) : DiffOp 𝕜 E F F 1 :=
  fun e fps ↦ fps 1 ![v e]

lemma lieDerivative_apply (f : E → F) (v : E → E) :
    diffOp_apply 𝕜 E F F (lieDerivative 𝕜 E F v) = (fun f e ↦ fderiv 𝕜 f e (v e)) := by
  ext f e
  simp [diffOp_apply, lieDerivative, ftaylorSeries]
  erw [iteratedFDeriv_one_apply ![v e] (𝕜 := 𝕜) (f := f) (x := e)]
  simp


variable (H)
/--
Gradient
-/
noncomputable def gradientDiffOp : DiffOp ℝ H ℝ H 1 := by
  let v := stdOrthonormalBasis ℝ H
  exact fun e fps ↦ ∑ i, fps 1 ![v i] • v i

lemma gradientDiffOp_apply (f : H → ℝ) :
    diffOp_apply ℝ H ℝ H (gradientDiffOp H) = ∇ := by
  ext g h
  simp [diffOp_apply, gradientDiffOp, ftaylorSeries]
  unfold gradient
  conv =>
    left
    arg 2
    intro i
    erw [iteratedFDeriv_one_apply (𝕜 := ℝ) (f := g) (x := h)]
  sorry

/--
Exterior derivative
-/
noncomputable def extDerivativeDiffOp [FiniteDimensional 𝕜 E] :
    DiffOp 𝕜 E 𝕜 (Module.Dual 𝕜 E) 1 := by
  let v := Module.finBasisOfFinrankEq 𝕜 E (rfl)
  exact fun e fps ↦ ∑ i, fps 1 ![v i] • (v.dualBasis i)

lemma extDerivativeOp_apply [FiniteDimensional 𝕜 E] (f : E → 𝕜) :
    diffOp_apply 𝕜 E 𝕜 (Module.Dual 𝕜 E) (extDerivativeDiffOp 𝕜 E) =
      0 := by
  let v := Module.finBasisOfFinrankEq 𝕜 E (rfl)
  ext g e
  simp [diffOp_apply, extDerivativeDiffOp, ftaylorSeries]
  conv =>
    left
    arg 2
    intro i
    sorry

/-!
## Examples: Differential Operators of Order ≤ 2
-/

noncomputable def laplaceDiffOp : DiffOp ℝ H ℝ ℝ 2 := by
  let v := stdOrthonormalBasis ℝ H
  exact fun e fps ↦ ∑ i, fps 2 ![v i, v i]

lemma laplaceDiffOp_apply [FiniteDimensional 𝕜 E] (f : E → 𝕜) :
    diffOp_apply ℝ H ℝ ℝ (laplaceDiffOp H) = Δ := by
  let v := stdOrthonormalBasis ℝ H
  ext g e
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [diffOp_apply, laplaceDiffOp, ftaylorSeries]
  rfl
