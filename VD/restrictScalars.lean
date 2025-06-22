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

def ContinuousMultilinearMap.restrictScalarsCLM
    (A : Type u_1) (R : Type uR) {ι : Type uι}
    {M₁ : ι → Type v₁}
    {M₂ : Type v₂}
    [Semiring R]
    [(i : ι) → AddCommMonoid (M₁ i)] [(i : ι) → Module R (M₁ i)]
    [∀ i, TopologicalSpace (M₁ i)]
    [AddCommMonoid M₂] [Module R M₂] [TopologicalSpace M₂]
    [Semiring A] [SMul R A]
    [(i : ι) → Module A (M₁ i)] [Module A M₂]
    [∀ (i : ι), IsScalarTower R A (M₁ i)] [IsScalarTower R A M₂]
    [SMulCommClass R R M₂] [SMulCommClass A R M₂] :
    (ContinuousMultilinearMap R M₁ M₂) →ₗ[R] (ContinuousMultilinearMap R M₁ M₂) where
      toFun := fun f ↦ f.restrictScalars R
      map_add' _ _ := by
        ext
        simp
      map_smul' _ _ := by
        ext
        simp


theorem fxx {n : ℕ} {x : E}
    {f : E → (ContinuousMultilinearMap ℂ (fun i : Fin n ↦ E) F)} :
    (fderiv ℝ ((ContinuousMultilinearMap.restrictScalars ℝ) ∘ f) x)
      = (ContinuousMultilinearMap.restrictScalars ℝ) ∘ ((fderiv ℂ f x).restrictScalars ℝ) := by
  ext a b
  simp
  have := fderiv ℝ (fun e ↦ (f e).restrictScalars ℝ) x
  have := fderiv ℂ (fun e ↦ (f e)) x
  have := (ContinuousMultilinearMap.restrictScalars ℝ) ∘ ((fderiv ℂ (fun e ↦ (f e)) x).restrictScalars ℝ)

  have := iteratedFDeriv ℂ n f x

  sorry

theorem ContDiffAt.iteratedFDeric_restrictScalars {f : E → F} {n : ℕ} {z : E}
    (h : ContDiffAt ℂ n f z) :
    (fun x : E ↦ ((iteratedFDeriv ℂ n f x).restrictScalars ℝ)) =ᶠ[𝓝 z]
      (fun x : E ↦ iteratedFDeriv ℝ n f x) := by
  induction n with
  | zero =>
    filter_upwards with a
    ext m
    simp [iteratedFDeriv_zero_apply m]
  | succ n hn =>
    have : ContDiffAt ℂ n f z := by
      apply h.of_le
      apply Nat.cast_le.mpr
      exact Nat.le_add_right n 1
    have t₀ := hn this
    have t₁ := this.eventually
    simp at t₁
    filter_upwards [t₀.eventually_nhds, t₁.eventually_nhds] with a h₁a h₂a
    ext m
    simp [iteratedFDeriv_succ_apply_left]

    have : (fun x ↦ (iteratedFDeriv ℂ n f x).restrictScalars ℝ) =ᶠ[𝓝 a] (fun x ↦ iteratedFDeriv ℝ n f x) := h₁a
    have := (this.fderiv (𝕜 := ℝ)).eq_of_nhds
    rw [← this]
    have s₀ : DifferentiableAt ℂ (iteratedFDeriv ℂ n f) a := by
      sorry
    have := s₀.fderiv_restrictScalars ℝ
    simp_all
    sorry
