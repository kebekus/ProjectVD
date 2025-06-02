import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Mul

open TensorProduct Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-!
# Mathlib.Analysis.Calculus.FDeriv.Mul
-/
theorem fderiv_const_clm_apply {x : E} {f : E → F} {c : F →L[𝕜] G} (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (c ∘ f) x = c ∘ (fderiv 𝕜 f x) := by
  let C : E → F →L[𝕜] G := fun e ↦ c
  have hC : DifferentiableAt 𝕜 C x := by
    exact differentiableAt_const c
  have t₀ := fderiv_clm_apply hC hf
  have : (fun y ↦ (C y) (f y)) = c ∘ f := by
    rfl
  rw [this] at t₀
  rw [t₀]
  have : C = Function.const E c := by rfl
  simp [fderiv_const, this]
  have : (0 : E →L[𝕜] F →L[𝕜] G).flip = 0 := by rfl
  simp [this]

/-!
# ContDiff.Basic
-/

theorem iteratedFDeriv_const_clm_apply
    {c : F →L[𝕜] G} {x : E} {f : E → F} (hf : ContDiff 𝕜 n f)
    {i : ℕ} (hi : i ≤ n) {x : E} {u : F}  :
    iteratedFDeriv 𝕜 i (c ∘ f) x = c ∘ (iteratedFDeriv 𝕜 i f x) := by
  induction i with
  | zero =>
    ext m
    simp [iteratedFDeriv_zero_apply]
  | succ a ia =>
    ext m
    rw [iteratedFDeriv_succ_apply_right]
    have : (iteratedFDeriv 𝕜 a (⇑c ∘ f) x) = ⇑c ∘ ⇑(iteratedFDeriv 𝕜 a f x) := by
      sorry
    simp_rw [this]
    sorry

/-!
# Main File Starts Here
-/

variable (𝕜) in
/--
Convenience reformulation of the second iterated derivative, as a map from `E`
to bilinear maps `E →ₗ[ℝ] E →ₗ[ℝ] ℝ
-/
noncomputable def bilinear_of_iteratedFDeriv_two (f : E → F) : E → E →ₗ[𝕜] E →ₗ[𝕜] F :=
  fun x ↦ (fderiv 𝕜 (fderiv 𝕜 f) x).toLinearMap₂

/--
Expression of `bilinear_of_iteratedFDeriv_two` in terms of `iteratedFDeriv`.
-/
lemma bilinear_of_iteratedFDeriv_two_eq_iteratedFDeriv (f : E → F) (e e₁ e₂ : E) :
    bilinear_of_iteratedFDeriv_two 𝕜 f e e₁ e₂ = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  simp [iteratedFDeriv_two_apply f e ![e₁, e₂], bilinear_of_iteratedFDeriv_two]

variable (𝕜) in
/--
Convenience reformulation of the second iterated derivative, as a map from `E`
to linear maps `E ⊗[𝕜] E →ₗ[𝕜] F`.
-/
noncomputable def tensor_of_iteratedFDeriv_two (f : E → F) : E → E ⊗[𝕜] E →ₗ[𝕜] F :=
  fun e ↦ lift (bilinear_of_iteratedFDeriv_two 𝕜 f e)

/--
Expression of `tensor_of_iteratedFDeriv_two` in terms of `iteratedFDeriv`.
-/
lemma tensor_of_iteratedFDeriv_two_eq_iteratedFDeriv (f : E → F) (e e₁ e₂ : E) :
    tensor_of_iteratedFDeriv_two 𝕜 f e (e₁ ⊗ₜ[𝕜] e₂) = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  rw [← bilinear_of_iteratedFDeriv_two_eq_iteratedFDeriv, tensor_of_iteratedFDeriv_two]
  rfl

variable (𝕜) in
/--
If two functions agree in a neighborhood, then so do their iterated derivatives.
-/
theorem Filter.EventuallyEq.iteratedFDeriv
    {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) (n : ℕ) :
    iteratedFDeriv 𝕜 n f₁ =ᶠ[𝓝 x] iteratedFDeriv 𝕜 n f₂ := by
  simp_all [← nhdsWithin_univ, ← iteratedFDerivWithin_univ,
    Filter.EventuallyEq.iteratedFDerivWithin]
