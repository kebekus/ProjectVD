import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-

Let E, F, G be vector spaces over nontrivally normed field 𝕜, a homogeneus
linear differential operator of order n is a map that attaches to every point e
of E a linear evaluation

{Continuous 𝕜-multilinear maps E → F in n variables} → G

In other words, homogeneus linear differential operator of order n is an
instance of the type:

D : E → (ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ E) F) →ₗ[𝕜] G

Given any map f : E → F, one obtains a map D f : E → G by sending a point e to
the evaluation (D e), applied to the n.th derivative of f at e

fun e ↦ D e (iteratedFDeriv 𝕜 n f e)

-/

@[ext]
class HomLinDiffOp
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (n : ℕ)
  (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
where
  tensorfield : E → ( E [×n]→L[𝕜] F) →L[𝕜] G
--  tensorfield : E → (ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ E) F) →ₗ[𝕜] G


namespace HomLinDiffOp

noncomputable def toFun
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  (o : HomLinDiffOp 𝕜 n E F G)
  : (E → F) → (E → G) :=
  fun f z ↦ o.tensorfield z (iteratedFDeriv 𝕜 n f z)


noncomputable def Laplace
  {𝕜 : Type*} [RCLike 𝕜]
  {n : ℕ}
  : HomLinDiffOp 𝕜 2 (EuclideanSpace 𝕜 (Fin n)) 𝕜 𝕜
  where
  tensorfield := by
    intro _

    let v := stdOrthonormalBasis 𝕜 (EuclideanSpace 𝕜 (Fin n))
    rw [finrank_euclideanSpace_fin] at v

    exact {
      toFun := fun f' ↦ ∑ i, f' ![v i, v i]
      map_add' := by
        intro f₁ f₂
        exact Finset.sum_add_distrib
      map_smul' := by
        intro m f
        exact Eq.symm (Finset.mul_sum Finset.univ (fun i ↦ f ![v i, v i]) m)
      cont := by
        apply continuous_finset_sum
        intro i _
        exact ContinuousEvalConst.continuous_eval_const ![v i, v i]
    }


noncomputable def Gradient
  {𝕜 : Type*} [RCLike 𝕜]
  {n : ℕ}
  : HomLinDiffOp 𝕜 1 (EuclideanSpace 𝕜 (Fin n)) 𝕜 (EuclideanSpace 𝕜 (Fin n))
  where
  tensorfield := by
    intro _

    let v := stdOrthonormalBasis 𝕜 (EuclideanSpace 𝕜 (Fin n))
    rw [finrank_euclideanSpace_fin] at v

    exact {
      toFun := fun f' ↦ ∑ i, (f' ![v i]) • (v i)
      map_add' := by
        intro f₁ f₂
        simp; simp_rw [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro m f
        simp; simp_rw [Finset.smul_sum, ←smul_assoc,smul_eq_mul]
      cont := by
        simp
        apply continuous_finset_sum
        intro i _
        apply Continuous.smul
        exact ContinuousEvalConst.continuous_eval_const ![v i]
        exact continuous_const
    }

end HomLinDiffOp
