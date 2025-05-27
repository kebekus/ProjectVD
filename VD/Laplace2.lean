import Mathlib.Analysis.InnerProductSpace.PiL2
--import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
import VD.IteratedFDeriv_two

open InnerProductSpace TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


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


noncomputable def Real.Laplace (f : E → E) : E → E :=
  fun x ↦ tensor_of_iteratedFDeriv_two ℝ f x (InnerProductSpace.canonicalCovariantTensor E)

notation "Δ" => Real.Laplace
