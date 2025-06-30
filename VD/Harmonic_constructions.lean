/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.Harmonic
import VD.ToMathlib.restrictScalars
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Construction of Harmonic Functions

This file constructs examples of harmonic functions.

- If `f` is holomorphic on the complex plane, then `f` is holomorphic, and so is
  its real part, imaginary part, and complex conjugate.

- If `f` is holomorphic without zero, then `log ‖f · ‖` is harmonic.
-/

open Topology

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f : ℂ → F} {x : ℂ}

/--
Holomorphic functions on ℂ are harmonic.
-/
theorem ContDiffAt.harmonicAt (h : ContDiffAt ℂ 2 f x) :
    HarmonicAt f x := by
  constructor
  · exact ContDiffAt.restrict_scalars ℝ h
  · filter_upwards [h.iteratedFDeriv_restrictScalars_eventuallyEq (𝕜 := ℝ)] with a ha
    have : (iteratedFDeriv ℂ 2 f a) (Complex.I • ![1, 1])
        = (∏ i, Complex.I) • ((iteratedFDeriv ℂ 2 f a) ![1, 1]) :=
      (iteratedFDeriv ℂ 2 f a).map_smul_univ (fun _ ↦ Complex.I) ![1, 1]
    simp_all [laplace_eq_iteratedFDeriv_complexPlane f, ← ha,
      ContinuousMultilinearMap.restrictScalarsLinear_apply,
      ContinuousMultilinearMap.coe_restrictScalars]

/--
Holomorphic functions on ℂ are harmonic.
-/
theorem AnalyticAt.harmonicAt [CompleteSpace F] (h : AnalyticAt ℂ f x) :
    HarmonicAt f x := h.contDiffAt.harmonicAt

/--
If `f : ℂ → ℂ` is holomorphic, then its real part is harmonic.
-/
theorem ContDiffAt.harmonicAt_realPart {f : ℂ → ℂ} (h : ContDiffAt ℂ 2 f x) :
  HarmonicAt (Complex.reCLM ∘ f) x := h.harmonicAt.comp_CLM

/--
If `f : ℂ → ℂ` is holomorphic, then its imaginary part is harmonic.
-/
theorem ContDiffAt.harmonicAt_imaginaryPart {f : ℂ → ℂ} (h : ContDiffAt ℂ 2 f x) :
  HarmonicAt (Complex.imCLM ∘ f) x := h.harmonicAt.comp_CLM

/--
If `f : ℂ → ℂ` is holomorphic, then its complex conjugate is harmonic.
-/
theorem ContDiffAt.harmonicAt_conjugate {f : ℂ → ℂ} (h : ContDiffAt ℂ 2 f x) :
  HarmonicAt (Complex.conjCLE ∘ f) x := harmonicAt_iff_harmonicAt_comp_CLE.1 h.harmonicAt


theorem log_normSq_of_holomorphicAt_is_harmonicAt
  {f : ℂ → ℂ}
  {z : ℂ}
  (h₁f : HolomorphicAt f z)
  (h₂f : f z ≠ 0) :
  HarmonicAt (Real.log ∘ Complex.normSq ∘ f) z := by

  -- For later use
  have slitPlaneLemma {z : ℂ} (hz : z ≠ 0) : z ∈ Complex.slitPlane ∨ -z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff, Complex.mem_slitPlane_iff]
    rw [ne_eq, Complex.ext_iff] at hz
    push_neg at hz
    simp_all only [ne_eq, Complex.zero_re, Complex.zero_im, Complex.neg_re, Left.neg_pos_iff,
      Complex.neg_im, neg_eq_zero]
    by_contra contra
    push_neg at contra
    exact hz (le_antisymm contra.1.1 contra.2.1) contra.1.2

  -- First prove the theorem for functions with image in the slitPlane
  have lem₁ : ∀ g : ℂ → ℂ, (HolomorphicAt g z) → (g z ≠ 0) → (g z ∈ Complex.slitPlane) → HarmonicAt (Real.log ∘ Complex.normSq ∘ g) z := by
    intro g h₁g h₂g h₃g

    -- Rewrite the log |g|² as Complex.log (g * gc)
    suffices hyp : HarmonicAt (Complex.log ∘ ((Complex.conjCLE ∘ g) * g)) z from by
      have : Real.log ∘ Complex.normSq ∘ g = Complex.reCLM ∘ Complex.ofRealCLM ∘ Real.log ∘ Complex.normSq ∘ g := by
        funext x
        simp
      rw [this]

      have : Complex.ofRealCLM ∘ Real.log ∘ Complex.normSq ∘ g = Complex.log ∘ ((Complex.conjCLE ∘ g) * g) := by
        funext x
        simp
        rw [Complex.ofReal_log]
        rw [Complex.normSq_eq_conj_mul_self]
        exact Complex.normSq_nonneg (g x)
      rw [← this] at hyp
      apply harmonicAt_comp_CLM_is_harmonicAt hyp

    -- Locally around z, rewrite Complex.log (g * gc) as Complex.log g + Complex.log.gc
    -- This uses the assumption that g z is in Complex.slitPlane
    have : (Complex.log ∘ (Complex.conjCLE ∘ g * g)) =ᶠ[nhds z] (Complex.log ∘ Complex.conjCLE ∘ g + Complex.log ∘ g) := by
      apply Filter.eventuallyEq_iff_exists_mem.2
      use g⁻¹' (Complex.slitPlane ∩ {0}ᶜ)
      constructor
      · apply ContinuousAt.preimage_mem_nhds
        · exact h₁g.differentiableAt.continuousAt
        · apply IsOpen.mem_nhds
          apply IsOpen.inter Complex.isOpen_slitPlane isOpen_ne
          constructor
          · exact h₃g
          · exact h₂g
      · intro x hx
        simp
        rw [Complex.log_mul_eq_add_log_iff _ hx.2]
        rw [Complex.arg_conj]
        simp [Complex.slitPlane_arg_ne_pi hx.1]
        constructor
        · exact Real.pi_pos
        · exact Real.pi_nonneg
        simp
        apply hx.2

    -- Locally around z, rewrite Complex.log (g * gc) as Complex.log g + Complex.log.gc
    -- This uses the assumption that g z is in Complex.slitPlane
    have : (Complex.log ∘ (Complex.conjCLE ∘ g * g)) =ᶠ[nhds z] (Complex.conjCLE ∘ Complex.log ∘ g + Complex.log ∘ g) := by
      apply Filter.eventuallyEq_iff_exists_mem.2
      use g⁻¹' (Complex.slitPlane ∩ {0}ᶜ)
      constructor
      · apply ContinuousAt.preimage_mem_nhds
        · exact h₁g.differentiableAt.continuousAt
        · apply IsOpen.mem_nhds
          apply IsOpen.inter Complex.isOpen_slitPlane isOpen_ne
          constructor
          · exact h₃g
          · exact h₂g
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

    rw [HarmonicAt_eventuallyEq this]
    apply harmonicAt_add_harmonicAt_is_harmonicAt
    · rw [← harmonicAt_iff_comp_CLE_is_harmonicAt]
      apply holomorphicAt_is_harmonicAt
      apply HolomorphicAt_comp
      use Complex.slitPlane, Complex.isOpen_slitPlane.mem_nhds h₃g,
        fun _ a ↦ Complex.differentiableAt_log a
      exact h₁g
    · apply holomorphicAt_is_harmonicAt
      apply HolomorphicAt_comp
      use Complex.slitPlane, Complex.isOpen_slitPlane.mem_nhds h₃g,
        fun _ a ↦ Complex.differentiableAt_log a
      exact h₁g

  by_cases h₃f : f z ∈ Complex.slitPlane
  · exact lem₁ f h₁f h₂f h₃f
  · have : Complex.normSq ∘ f = Complex.normSq ∘ (-f) := by funext; simp
    rw [this]
    apply lem₁ (-f)
    · exact HolomorphicAt_neg h₁f
    · simpa
    · exact (slitPlaneLemma h₂f).resolve_left h₃f


theorem logabs_of_holomorphicAt_is_harmonic
  {f : ℂ → ℂ}
  {z : ℂ}
  (h₁f : HolomorphicAt f z)
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
