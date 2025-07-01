/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.Harmonic
import VD.ToMathlib.restrictScalars
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Construction of Harmonic Functions

This file constructs examples of harmonic functions.

- If `f` is holomorphic on the complex plane, then `f` is holomorphic, and so is
  its real part, imaginary part, and complex conjugate.

- If `f` is holomorphic without zero, then `log ‖f ·‖` is harmonic.
-/

open Complex Topology

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f : ℂ → F} {x : ℂ}

/-!
## Harmonicity of Analytic Functions
-/

/--
Continuously complex-differentiable functions on ℂ are harmonic.
-/
theorem ContDiffAt.harmonicAt (h : ContDiffAt ℂ 2 f x) : HarmonicAt f x := by
  constructor
  · exact h.restrict_scalars ℝ
  · filter_upwards [h.iteratedFDeriv_restrictScalars_eventuallyEq (𝕜 := ℝ)] with a ha
    have : (iteratedFDeriv ℂ 2 f a) (I • ![1, 1])
        = (∏ i, I) • ((iteratedFDeriv ℂ 2 f a) ![1, 1]) :=
      (iteratedFDeriv ℂ 2 f a).map_smul_univ (fun _ ↦ I) ![1, 1]
    simp_all [laplace_eq_iteratedFDeriv_complexPlane f, ← ha,
      ContinuousMultilinearMap.restrictScalarsLinear_apply,
      ContinuousMultilinearMap.coe_restrictScalars]

/--
Analytic functions on ℂ are harmonic.
-/
theorem AnalyticAt.harmonicAt [CompleteSpace F] (h : AnalyticAt ℂ f x) :
    HarmonicAt f x := h.contDiffAt.harmonicAt

/--
If `f : ℂ → ℂ` is complex-analytic, then its real part is harmonic.
-/
theorem ContDiffAt.harmonicAt_realPart {f : ℂ → ℂ} (h : AnalyticAt ℂ f x) :
    HarmonicAt (reCLM ∘ f) x := h.harmonicAt.comp_CLM

/--
If `f : ℂ → ℂ` is complex-analytic, then its imaginary part is harmonic.
-/
theorem ContDiffAt.harmonicAt_imaginaryPart {f : ℂ → ℂ} (h : AnalyticAt ℂ f x) :
  HarmonicAt (imCLM ∘ f) x := h.harmonicAt.comp_CLM

/--
If `f : ℂ → ℂ` is complex-analytic, then its complex conjugate is harmonic.
-/
theorem ContDiffAt.harmonicAt_conjugate {f : ℂ → ℂ} (h : AnalyticAt ℂ f x) :
  HarmonicAt (conjCLE ∘ f) x := harmonicAt_iff_harmonicAt_comp_CLE.1 h.harmonicAt

/-!
## Harmonicity of `log ‖analytic‖`
-/

/- Helper lemma for -/
private lemma slitPlaneLemma {z : ℂ} (hz : z ≠ 0) : z ∈ slitPlane ∨ -z ∈ slitPlane := by
  rw [mem_slitPlane_iff, mem_slitPlane_iff]
  rw [ne_eq, Complex.ext_iff] at hz
  push_neg at hz
  simp_all only [ne_eq, zero_re, zero_im, neg_re, Left.neg_pos_iff, neg_im, neg_eq_zero]
  by_contra contra
  push_neg at contra
  exact hz (le_antisymm contra.1.1 contra.2.1) contra.1.2

private lemma lem₁ {z : ℂ} {g : ℂ → ℂ} (h₁g : AnalyticAt ℂ g z) (h₂g : g z ≠ 0) (h₃g : g z ∈ slitPlane) :
    HarmonicAt (Real.log ∘ normSq ∘ g) z := by

  -- Rewrite the log |g|² as Complex.log (g * gc)
  suffices hyp : HarmonicAt (log ∘ ((conjCLE ∘ g) * g)) z from by
    have : Real.log ∘ normSq ∘ g = reCLM ∘ ofRealCLM ∘ Real.log ∘ normSq ∘ g := by aesop
    rw [this]
    have : ofRealCLM ∘ Real.log ∘ normSq ∘ g = log ∘ ((conjCLE ∘ g) * g) := by
      funext x
      simp only [Function.comp_apply, ofRealCLM_apply, Pi.mul_apply, conjCLE_apply]
      rw [ofReal_log, normSq_eq_conj_mul_self]
      exact normSq_nonneg (g x)
    rw [← this] at hyp
    apply hyp.comp_CLM

  have t₀ : g ⁻¹' (slitPlane ∩ {0}ᶜ) ∈ 𝓝 z := by
    apply h₁g.differentiableAt.continuousAt.preimage_mem_nhds
    exact (isOpen_slitPlane.inter isOpen_ne).mem_nhds ⟨h₃g, h₂g⟩

  -- Locally around z, rewrite Complex.log (g * gc) as Complex.log g + Complex.log.gc
  -- This uses the assumption that g z is in Complex.slitPlane
  have : (log ∘ (conjCLE ∘ g * g)) =ᶠ[𝓝 z] (log ∘ conjCLE ∘ g + log ∘ g) := by
    filter_upwards [t₀] with x hx
    simp only [Function.comp_apply, Pi.mul_apply, conjCLE_apply, Pi.add_apply]
    rw [Complex.log_mul_eq_add_log_iff _ hx.2, Complex.arg_conj]
    simp only [Complex.slitPlane_arg_ne_pi hx.1, ↓reduceIte, neg_add_cancel, Set.mem_Ioc,
      Left.neg_neg_iff, Real.pi_pos, Real.pi_nonneg, and_self]
    simpa [ne_eq, map_eq_zero] using hx.2

  -- Locally around z, rewrite Complex.log (g * gc) as Complex.log g + Complex.log.gc
  -- This uses the assumption that g z is in Complex.slitPlane
  have : (log ∘ (conjCLE ∘ g * g)) =ᶠ[𝓝 z] (conjCLE ∘ log ∘ g + log ∘ g) := by
    apply Filter.eventuallyEq_iff_exists_mem.2
    use g⁻¹' (Complex.slitPlane ∩ {0}ᶜ), t₀
    · intro x hx
      simp
      rw [← Complex.log_conj]
      rw [Complex.log_mul_eq_add_log_iff _ hx.2]
      rw [Complex.arg_conj]
      simp [Complex.slitPlane_arg_ne_pi hx.1]
      constructor
      · exact Real.pi_pos
      · exact Real.pi_nonneg
      simp
      apply hx.2
      apply Complex.slitPlane_arg_ne_pi hx.1

  rw [harmonicAt_congr_nhds this]
  apply HarmonicAt.add
  · rw [← harmonicAt_iff_harmonicAt_comp_CLE]
    apply AnalyticAt.harmonicAt
    apply AnalyticAt.comp
    · apply analyticAt_clog h₃g
    · exact h₁g
  · apply AnalyticAt.harmonicAt
    apply AnalyticAt.comp
    · apply analyticAt_clog h₃g
    · exact h₁g

theorem log_normSq_of_holomorphicAt_is_harmonicAt
  {f : ℂ → ℂ}
  {z : ℂ}
  (h₁f : AnalyticAt ℂ f z)
  (h₂f : f z ≠ 0) :
  HarmonicAt (Real.log ∘ Complex.normSq ∘ f) z := by


  -- First prove the theorem for functions with image in the slitPlane

  by_cases h₃f : f z ∈ Complex.slitPlane
  · exact lem₁ h₁f h₂f h₃f
  · have : Complex.normSq ∘ f = Complex.normSq ∘ (-f) := by funext; simp
    rw [this]
    apply lem₁ h₁f.neg
    · simpa
    · exact (slitPlaneLemma h₂f).resolve_left h₃f


theorem logabs_of_holomorphicAt_is_harmonic
  {f : ℂ → ℂ}
  {z : ℂ}
  (h₁f : AnalyticAt ℂ f z)
  (h₂f : f z ≠ 0) :
  HarmonicAt (fun w ↦ Real.log ‖f w‖) z := by

  -- Suffices: Harmonic (2⁻¹ • Real.log ∘ ⇑Complex.normSq ∘ f)
  have : (fun z ↦ Real.log ‖f z‖) = (2 : ℝ)⁻¹ • (Real.log ∘ Complex.normSq ∘ f) := by
    funext z
    simp
    rw [Complex.norm_def]
    rw [Real.log_sqrt]
    linarith
    exact Complex.normSq_nonneg (f z)
  rw [this]

  -- Suffices: Harmonic (Real.log ∘ ⇑Complex.normSq ∘ f)
  apply (harmonicAt_iff_smul_const_is_harmonicAt (inv_ne_zero two_ne_zero)).1
  exact log_normSq_of_holomorphicAt_is_harmonicAt h₁f h₂f
