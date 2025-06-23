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

theorem fxx {n : ℕ} {x : E}
    {f : E → (ContinuousMultilinearMap ℂ (fun i : Fin n ↦ E) F)}
    (h : DifferentiableAt ℂ f x) :
    (fderiv ℝ ((ContinuousMultilinearMap.restrictScalarsLinear ℝ) ∘ f) x)
      = (ContinuousMultilinearMap.restrictScalars ℝ) ∘ ((fderiv ℂ f x).restrictScalars ℝ) := by
  rw [fderiv_comp]
  rw [ContinuousLinearMap.fderiv]
  simp
  ext a b
  simp
  have := h.fderiv_restrictScalars ℝ
  rw [this]
  simp
  fun_prop
  exact h.restrictScalars ℝ


theorem ContDiffAt.differentiableAt_iteratedDeriv
    {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {F : Type u_2} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → F} {x : 𝕜} {n : WithTop ℕ∞} {m : ℕ}
    (h : ContDiffAt 𝕜 n f x) (hmn : m < n) :
    DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 m f) x := by
  apply ContDiffAt.differentiableAt (n := 1)
  apply h.iteratedFDeriv_right (i := m) (m := 1)
  cases n
  · simp
  · apply add_le_of_add_le_left
    · obtain ⟨b, rfl⟩ := WithTop.ne_top_iff_exists.1 ha
      sorry
    · sorry
  · rfl

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
    filter_upwards [t₀.eventually_nhds, t₁.eventually_nhds] with a h₁a h₂a
    rw [← Filter.EventuallyEq] at h₁a
    ext m
    simp [iteratedFDeriv_succ_apply_left]
    have := h₁a.fderiv_eq (𝕜 := ℝ)
    rw [← this]
    rw [fxx]
    simp
    · have := h.differentiableAt_iteratedDeriv (m := n)

      sorry


theorem ContDiffAt.harmonicAt  {f : ℂ → F} {x : ℂ} (h : ContDiffAt ℂ 2 f x) :
    HarmonicAt f x := by
  constructor
  · exact ContDiffAt.restrict_scalars ℝ h
  · filter_upwards [h.iteratedFDeric_restrictScalars] with a ha
    rw [laplace_eq_iteratedFDeriv_complexPlane f]
    simp
    rw [← ha]
    simp

    sorry
