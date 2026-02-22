import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Harmonic.Analytic

open Asymptotics Classical Complex ComplexConjugate Filter Function Metric Real Set Classical Topology
set_option backward.isDefEq.respectTransparency false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}

/--
**Morera's theorem for the complex plane** A continuous function on `ℂ` whose
integrals on rectangles vanish, has primitives.
-/
theorem Complex.IsConservativeOn.isExactOn_univ [CompleteSpace E]
    (hf' : Continuous f)
    (hf : IsConservativeOn f univ) :
    IsExactOn f univ := by
  use fun z ↦ wedgeIntegral 0 z f
  intro z hz
  have h₁z : z ∈ ball 0 (‖z‖ + 1) := by aesop
  have h₁f : IsConservativeOn f (ball 0 (‖z‖ + 1)) := by
    apply hf.mono (by tauto)
  have h₂f : ContinuousOn f (ball 0 (‖z‖ + 1)) := by fun_prop
  exact h₁f.hasDerivAt_wedgeIntegral h₂f h₁z

/--
**Morera's theorem for the complex plane** A holomorphic function on `ℂ` has
primitives.
-/
theorem _root_.Differentiable.isExactOn_univ
    [CompleteSpace E]
    (hf : Differentiable ℂ f) :
    IsExactOn f univ := by
  apply Complex.IsConservativeOn.isExactOn_univ hf.continuous
    ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).2
      hf.differentiableOn).1

/--
If a function `f : ℂ → ℝ` is harmonic, then `f` is the real part of a
holomorphic function.
-/
theorem InnerProductSpace.harmonic_is_realOfHolomorphic_univ {f : ℂ → ℝ}
    (hf : HarmonicOnNhd f univ) :
    ∃ F : ℂ → ℂ, (AnalyticOnNhd ℂ F univ) ∧ ((fun z ↦ (F z).re) = f) := by
  let g := ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)
  have hg : Differentiable ℂ g :=
    fun x ↦ (HarmonicAt.differentiableAt_complex_partial (hf x (mem_univ x)))
  obtain ⟨F₀, hF₀⟩ := hg.isExactOn_univ
  let F := fun x ↦ F₀ x - F₀ 0 + f 0
  have h₁F : ∀ z₁, HasDerivAt F (g z₁) z₁ := by
    simp_all [F]
  have h₂F : Differentiable ℂ F :=
    fun x ↦ (h₁F x).differentiableAt
  have h₃F : Differentiable ℝ F :=
    h₂F.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
  use F, (h₂F.differentiableOn).analyticOnNhd isOpen_univ
  rw [(by aesop : (fun z ↦ (F z).re) = Complex.reCLM ∘ F)]
  ext x
  apply (convex_univ).eqOn_of_fderivWithin_eq (𝕜 := ℝ) (x := 0)
  · fun_prop
  · exact fun y hy ↦ ((hf y hy).1.differentiableAt two_ne_zero).differentiableWithinAt
  · exact isOpen_univ.uniqueDiffOn
  · intro y hy
    have h₄F := (h₁F y).differentiableAt
    have h₅F := h₄F.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
    rw [fderivWithin_eq_fderiv (isOpen_univ.uniqueDiffWithinAt hy)
      (reCLM.differentiableAt.comp y h₅F), fderiv_comp y (by fun_prop) h₅F,
      ContinuousLinearMap.fderiv, h₄F.fderiv_restrictScalars (𝕜 := ℝ)]
    ext a
    nth_rw 2 [(by simp : a = a.re • (1 : ℂ) + a.im • (I : ℂ))]
    rw [map_add, map_smul, map_smul]
    simp [HasDerivAt.deriv (h₁F y), g]
  · simp_all
  · simp [F]
  · tauto

@[grind . ] lemma re_eq_re_if_cexp_eq_cexp {a b : ℂ} (h : cexp a = cexp b) :
    a.re = b.re := by
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 h
  simp [hn]

/-
**Liouville's theorem for harmonic functions on the complex plane** A
real-valued, bounded harmonic function on the complex plane is constant.
-/
theorem InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant
    (f : ℂ → ℝ)
    (h_harm : HarmonicOnNhd f univ)
    (h_bound : Bornology.IsBounded (range f)) :
    ∀ z w, f z = f w := by
  -- By assumption, there exists a holomorphic function $f$ such that $\Re(f) = u$.
  obtain ⟨F, hF_diff, hF_re⟩ := harmonic_is_realOfHolomorphic_univ h_harm
  -- Since $g(z)$ is bounded, by Liouville's theorem, $g(z)$ is constant.
  have hg_const : ∀ z w, Complex.exp (F z) = Complex.exp (F w) := by
    apply Differentiable.apply_eq_apply_of_bounded
    apply (differentiable_exp.comp (fun x ↦ (hF_diff x (mem_univ x)).differentiableAt))
    rw [isBounded_iff_forall_norm_le] at *
    obtain ⟨M, hM⟩ := h_bound
    use exp M
    simp_all only [mem_range, norm_eq_abs, forall_exists_index, forall_apply_eq_imp_iff,
      norm_exp, exp_le_exp]
    rw [← hF_re] at hM
    grind
  grind
