import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
--import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
import VD.IteratedFDeriv_two

open InnerProductSpace TensorProduct Topology

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]


variable (E) in
/--
The canonical covariant tensor corresponding to `InnerProductSpace.canonicalContravariantTensor`
under the identification of `E` with its dual.
-/
noncomputable def InnerProductSpace.canonicalCovariantTensor :
    E ⊗[ℝ] E := ∑ i, ((stdOrthonormalBasis ℝ E) i) ⊗ₜ[ℝ] ((stdOrthonormalBasis ℝ E) i)

/-- Representation of the canonical covariant tensor in terms of an orthonormal basis. -/
theorem InnerProductSpace.canonicalCovariantTensor_eq_sum
    {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) :
    InnerProductSpace.canonicalCovariantTensor E = ∑ i, (v i) ⊗ₜ[ℝ] (v i) := by
  let w := stdOrthonormalBasis ℝ E
  calc ∑ m, w m ⊗ₜ[ℝ] w m
  _ = ∑ m, ∑ n, ⟪w m, w n⟫_ℝ • w m ⊗ₜ[ℝ] w n := by
    congr 1 with m
    rw [Fintype.sum_eq_single m _, orthonormal_iff_ite.1 w.orthonormal]
    · simp only [↓reduceIte, one_smul]
    simp only [orthonormal_iff_ite.1 w.orthonormal, ite_smul, one_smul, zero_smul,
      ite_eq_right_iff]
    tauto
  _ = ∑ m, ∑ n, (∑ i, ⟪w m, v i⟫_ℝ * ⟪v i, w n⟫_ℝ) • w m ⊗ₜ[ℝ] w n := by
    simp_rw [OrthonormalBasis.sum_inner_mul_inner v]
  _ = ∑ m, ∑ n, (∑ i, ⟪w m, v i⟫_ℝ * ⟪w n, v i⟫_ℝ) • w m ⊗ₜ[ℝ] w n := by
    simp only [real_inner_comm (w _)]
  _ = ∑ i, (∑ m, ⟪w m, v i⟫_ℝ • w m) ⊗ₜ[ℝ] ∑ n, ⟪w n, v i⟫_ℝ • w n := by
    simp only [sum_tmul, tmul_sum, smul_tmul_smul, Finset.sum_comm (γ := ι), Finset.sum_smul]
    rw [Finset.sum_comm]
  _ = ∑ i, v i ⊗ₜ[ℝ] v i := by
    simp only [w.sum_repr' (v _)]


noncomputable def Laplace (f : E → F) : E → F :=
  fun x ↦ tensor_of_iteratedFDeriv_two ℝ f x (InnerProductSpace.canonicalCovariantTensor E)

notation "Δ" => Laplace

/--
Standard formula, computing the Laplace operator from any orthonormal basis.
-/
theorem laplace_eq_iteratedFDeriv {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) (f : E → F) :
    Δ f = fun x ↦ ∑ i, iteratedFDeriv ℝ 2 f x ![v i, v i] := by
  ext x
  simp [Laplace, InnerProductSpace.canonicalCovariantTensor_eq_sum v,
    tensor_of_iteratedFDeriv_two_eq_iteratedFDeriv]

/-!
# TODO: Computation of Laplace in terms of standard basis, for ℝ^n, ℂ^n and ℂ
-/

/-!
## Congruence Lemmata
-/

variable {f f₁ f₂ : E → F} {x : E}

theorem laplace_eventuallyEq' (h : f₁ =ᶠ[𝓝 x] f₂) : Δ f₁ =ᶠ[𝓝 x] Δ f₂ := by
  sorry

/-!
## ℂ-Linearity on Continuously Differentiable Functions
-/

theorem ContDiffAt.laplace_add_nhd (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) =ᶠ[𝓝 x] (Δ f₁) + (Δ f₂):= by
  sorry

theorem ContDiffAt.laplace_add (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) x = (Δ f₁) x + (Δ f₂) x := by
  sorry

theorem ContDiffAt.laplace_sub_nhd (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ - f₂) =ᶠ[𝓝 x] (Δ f₁) - (Δ f₂):= by
  sorry

theorem ContDiffAt.laplace_sub (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ - f₂) x = (Δ f₁) x - (Δ f₂) x := by
  sorry

theorem laplace_smul : ∀ v : ℝ, Δ (v • f) = v • (Δ f) := by
  sorry

/-!
## Commutativity with Linear Operators

This section establishes commutativity with linear operators, showing in
particular that Δ commutes with taking real and imaginary parts of
complex-valued functions.
-/

theorem ContDiffAt.laplace_CLM_comp {l : F →L[ℝ] G} (h : ContDiffAt ℝ 2 f x) :
    Δ (l ∘ f) x = (l ∘ (Δ f)) x := by
  sorry

theorem laplace_CLE_comp {l : F ≃L[ℝ] G} :
    Δ (l ∘ f) = l ∘ (Δ f) := by
  sorry
