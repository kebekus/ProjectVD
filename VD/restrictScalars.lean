import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import VD.Harmonic

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : ℂ → F}
  {s t : Set E} {c : ℝ}

open Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem fderiv_restrictScalarsLinear_comp {n : ℕ} {x : E}
    {f : E → (ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ E) F)}
    (h : DifferentiableAt ℂ f x) :
    (fderiv ℝ ((ContinuousMultilinearMap.restrictScalarsLinear ℝ) ∘ f) x)
      = (ContinuousMultilinearMap.restrictScalars ℝ) ∘ ((fderiv ℂ f x).restrictScalars ℝ) := by
  rw [fderiv_comp _ (by fun_prop) (h.restrictScalars ℝ), ContinuousLinearMap.fderiv]
  ext a b
  simp [h.fderiv_restrictScalars ℝ]

theorem ContDiffAt.differentiableAt_iteratedDeriv
    {f : E → F} {x : E} {n : ℕ} {m : ℕ}
    (h : ContDiffAt ℂ n f x) (hmn : m < n) :
    DifferentiableAt ℂ (iteratedFDeriv ℂ m f) x := by
  apply ContDiffAt.differentiableAt (n := 1)
  apply h.iteratedFDeriv_right (i := m) (m := 1)
  rw [Nat.lt_iff_add_one_le, add_comm] at hmn
  rw [← WithTop.coe_one]
  simp_all
  sorry
  sorry

theorem ContDiffAt.iteratedFDeriv_restrictScalars {f : E → F} {n : ℕ} {z : E}
    (h : ContDiffAt ℂ n f z) :
    (ContinuousMultilinearMap.restrictScalarsLinear ℝ) ∘ (iteratedFDeriv ℂ n f) =ᶠ[𝓝 z]
      (iteratedFDeriv ℝ n f) := by
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
    filter_upwards [t₀.eventually_nhds, t₁.eventually_nhds,
      h.eventually (by simp)] with a h₁a h₂a h₃a
    rw [← Filter.EventuallyEq] at h₁a
    ext m
    simp [iteratedFDeriv_succ_apply_left]
    have := h₁a.fderiv_eq (𝕜 := ℝ)
    rw [← this]
    rw [fderiv_restrictScalarsLinear_comp]
    simp
    · apply h₃a.differentiableAt_iteratedDeriv (m := n)
      simp
