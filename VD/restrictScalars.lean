import Mathlib.LinearAlgebra.Multilinear.Basic
import VD.Harmonic
import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Topology.Algebra.Module.Multilinear.Topology

def MultilinearMap.restrictScalarsLM
    (A : Type u_1) (R : Type uR) {ι : Type uι}
    {M₁ : ι → Type v₁}
    {M₂ : Type v₂}
    [Semiring R]
    [(i : ι) → AddCommMonoid (M₁ i)] [(i : ι) → Module R (M₁ i)]
    [AddCommMonoid M₂] [Module R M₂]
    [Semiring A] [SMul R A]
    [(i : ι) → Module A (M₁ i)] [Module A M₂]
    [∀ (i : ι), IsScalarTower R A (M₁ i)] [IsScalarTower R A M₂]
    [SMulCommClass R R M₂] [SMulCommClass A R M₂] :
    (MultilinearMap A M₁ M₂) →ₗ[R] (MultilinearMap R M₁ M₂) where
      toFun := fun f ↦ f.restrictScalars R
      map_add' _ _ := by
        ext
        simp
      map_smul' _ _ := by
        ext
        simp

set_option diagnostics true

def ContinuousMultilinearMap.restrictScalarsCLM
    (A : Type u_1) (R : Type uR) {ι : Type uι}
    {M₁ : ι → Type v₁}
    {M₂ : Type v₂}
    [NormedField R]
    [(i : ι) → TopologicalSpace (M₁ i)] [(i : ι) → AddCommGroup (M₁ i)] [(i : ι) → Module R (M₁ i)]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂]
    [ContinuousAdd M₂] [ContinuousConstSMul R M₂] [TopologicalSpace M₂] [IsTopologicalAddGroup M₂]
    [SMulCommClass R R M₂]
    /-
    [Semiring A] [SMul R A]
    [(i : ι) → Module A (M₁ i)] [Module A M₂]
    [∀ (i : ι), IsScalarTower R A (M₁ i)] [IsScalarTower R A M₂]
    [SMulCommClass R R M₂] [SMulCommClass A R M₂]
    -/ :
    (ContinuousMultilinearMap R M₁ M₂) →L[R] (ContinuousMultilinearMap R M₁ M₂) where
      toFun := fun f ↦ f.restrictScalars R
      map_add' _ _ := by
        ext
        simp
      map_smul' _ _ := by
        ext
        simp
