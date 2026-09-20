/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.OpenMapping
import VD.MathlibPending.PoissonJensen
import VD.MathlibSubmitted.CanonicalFactor

/-!
# Differentiated Poisson Representation — LLD work package B4

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §4.

Mathlib target: extend `Mathlib/Analysis/Complex/Poisson.lean` (B4).
Dependencies: the derivative of the Herglotz–Riesz kernel integral (B1–B3, now in Mathlib:
`hasDerivAt_circleAverage_herglotzRieszKernel_smul` in `Mathlib/Analysis/Complex/Poisson.lean`)
and the Poisson–Jensen chain (the extended canonical decomposition is now in Mathlib, in
`Mathlib/Analysis/Complex/CanonicalDecomposition.lean`; see also
`VD/MathlibPending/PoissonJensen.lean`).

- `MeromorphicOn.logDeriv_eq_circleAverage` (B4): if `h` is meromorphic on the closed ball,
  analytic and nonvanishing on the **open** ball, then its logarithmic derivative at interior
  points is the circle average of `log ‖h ·‖` against the `w`-derivative of the Herglotz–Riesz
  kernel. Proof: the kernel integral `F` is analytic in the pole with computable derivative
  (Mathlib); its real part is `log ‖h ·‖` by Poisson–Jensen; `logDeriv h` has a primitive `G` on
  the ball (`DifferentiableOn.isExactOn_ball`), so `h = κ · exp G`; then `F - G` has constant
  real part, hence is constant (`AnalyticOnNhd.eq_const_of_re_eq_const`), and differentiating
  gives the claim.

- `circleAverage_smul_log_norm_sub_sphere` (B4, boundary special case): since nonvanishing is
  required only on the *open* ball, the theorem applies to `h = (· - u)` with `u` **on the
  sphere**, yielding the boundary-divisor correction
  `circleAverage (fun ζ ↦ (2ζ/(ζ-w)²) • log ‖ζ - u‖) 0 R = (w - u)⁻¹` for free.

Work package B5, the logarithmic derivative of the canonical factor
(`Complex.logDeriv_canonicalFactor`, `Complex.norm_logDeriv_canonicalFactor_le`), has been split
off into `VD/MathlibSubmitted/CanonicalFactor.lean` and is in review; this file imports it.
-/

open Complex ComplexConjugate Filter Function MeromorphicOn Metric Real Set

/-!
## The Derived Herglotz–Riesz Kernel
-/

/-- The `w`-derivative `2ζ/(ζ - w)²` of the Herglotz–Riesz kernel `herglotzRieszKernel 0 w ζ`
centred at the origin; see `hasDerivAt_circleAverage_herglotzRieszKernel_smul`. Integrating
`log ‖f ·‖` against it over a circle produces the logarithmic derivative of `f`. -/
noncomputable def derivHerglotzRieszKernel (w ζ : ℂ) : ℂ := 2 * ζ / (ζ - w) ^ 2

lemma derivHerglotzRieszKernel_def (w ζ : ℂ) :
    derivHerglotzRieszKernel w ζ = 2 * ζ / (ζ - w) ^ 2 := rfl

lemma derivHerglotzRieszKernel_fun_def (w : ℂ) :
    derivHerglotzRieszKernel w = fun ζ ↦ 2 * ζ / (ζ - w) ^ 2 := rfl

/-!
## B4: The Differentiated Poisson Representation
-/

/-- **Differentiated Poisson representation**: if `h` is meromorphic on the closed ball, analytic
and nonvanishing on the open ball, then its logarithmic derivative at interior points is the
circle average of `log ‖h ·‖` against the `w`-derivative of the Herglotz–Riesz kernel. -/
theorem MeromorphicOn.logDeriv_eq_circleAverage {h : ℂ → ℂ} {R : ℝ} {w : ℂ}
    (h₁ : MeromorphicOn h (closedBall 0 R)) (h₂ : AnalyticOnNhd ℂ h (ball 0 R))
    (h₃ : ∀ z ∈ ball 0 R, h z ≠ 0) (hw : w ∈ ball 0 R) :
    logDeriv h w
      = circleAverage (fun ζ ↦ derivHerglotzRieszKernel w ζ • (Real.log ‖h ζ‖ : ℂ)) 0 R := by
  have hR : 0 < R := pos_of_mem_ball hw
  -- Points of the open ball lie off the circle
  have hball : ∀ z ∈ ball (0 : ℂ) R, z ∉ sphere 0 |R| := fun z hz hs ↦ by
    rw [mem_ball_zero_iff] at hz
    rw [mem_sphere_zero_iff_norm, abs_of_pos hR] at hs
    exact hz.ne hs
  -- Integrability of `log ‖h ·‖`, real and complex-valued
  have hgR : CircleIntegrable (fun ζ ↦ Real.log ‖h ζ‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm
      (h₁.mono_set (by rw [abs_of_pos hR]; exact sphere_subset_closedBall))
  have hgC : CircleIntegrable (fun ζ ↦ (Real.log ‖h ζ‖ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hgR ⊢
    exact Complex.ofRealCLM.integrable_comp hgR
  -- The Herglotz–Riesz kernel integral `F`
  set F : ℂ → ℂ :=
    fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (Real.log ‖h ζ‖ : ℂ)) 0 R
    with hF_def
  have hF_deriv : ∀ z ∈ ball 0 R, HasDerivAt F
      (circleAverage (fun ζ ↦ (2 * ζ / (ζ - z) ^ 2) • (Real.log ‖h ζ‖ : ℂ)) 0 R) z :=
    fun z hz ↦ hasDerivAt_circleAverage_herglotzRieszKernel_smul hgC (hball z hz)
  have hF_an : AnalyticOnNhd ℂ F (ball 0 R) :=
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hgC).mono fun z hz ↦ hball z hz
  -- The real part of `F` is `log ‖h ·‖`, by Poisson–Jensen
  have horder : ∀ z ∈ ball 0 R, meromorphicOrderAt h z = 0 := by
    intro z hz
    rw [(h₂ z hz).meromorphicOrderAt_eq, (h₂ z hz).analyticOrderAt_eq_zero.2 (h₃ z hz)]
    rfl
  have hdiv : ∀ i, (divisor h (ball 0 R)) i = 0 := by
    intro i
    by_cases hi : i ∈ ball 0 R
    · rw [(h₁.mono_set ball_subset_closedBall).divisor_apply hi, horder i hi]
      rfl
    · by_contra hne
      exact hi ((divisor h (ball 0 R)).supportWithinDomain (mem_support.2 hne))
  have hRe : ∀ z ∈ ball 0 R, (F z).re = Real.log ‖h z‖ := by
    intro z hz
    rw [hF_def]
    rw [re_circleAverage_herglotzRieszKernel_smul hgR (hball z hz)]
    have hPJ := h₁.log_norm_meromorphicTrailingCoeffAt hz (horder z hz)
    rw [(h₂ z hz).meromorphicTrailingCoeffAt_of_ne_zero (h₃ z hz)] at hPJ
    have hsum : (∑ᶠ i, ((divisor h (ball 0 R)) i)
        * Real.log ‖Complex.canonicalFactor R (i - 0) (z - 0)‖) = 0 := by
      simp [hdiv]
    rw [hsum, sub_zero] at hPJ
    exact hPJ.symm
  -- A primitive `G` of `logDeriv h` on the ball
  have hld_an : AnalyticOnNhd ℂ (logDeriv h) (ball 0 R) :=
    fun z hz ↦ ((h₂ z hz).deriv).div (h₂ z hz) (h₃ z hz)
  obtain ⟨G, hG⟩ := hld_an.differentiableOn.isExactOn_ball
  -- The multiplicative representation `h = κ · exp G`
  have hφ : ∀ z ∈ ball 0 R, HasDerivAt (fun z ↦ h z * Complex.exp (-G z)) 0 z := by
    intro z hz
    have d₁ : HasDerivAt h (deriv h z) z := (h₂ z hz).differentiableAt.hasDerivAt
    have d₂ : HasDerivAt (fun z ↦ Complex.exp (-G z))
        (Complex.exp (-G z) * -logDeriv h z) z := ((hG z hz).neg).cexp
    have hz0 : h z ≠ 0 := h₃ z hz
    have d₃ := d₁.mul d₂
    have hval : deriv h z * Complex.exp (-G z)
        + h z * (Complex.exp (-G z) * -logDeriv h z) = 0 := by
      rw [logDeriv_apply]
      field_simp
      ring
    rw [hval] at d₃
    exact d₃
  obtain ⟨κ, hκ⟩ := isOpen_ball.exists_is_const_of_deriv_eq_zero
    (convex_ball (0:ℂ) R).isPreconnected
    (fun z hz ↦ (hφ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hφ z hz).deriv)
  have hκ_ne : κ ≠ 0 := by
    rw [← hκ w hw]
    exact mul_ne_zero (h₃ w hw) (Complex.exp_ne_zero _)
  have h_rep : ∀ z ∈ ball 0 R, h z = κ * Complex.exp (G z) := by
    intro z hz
    rw [← hκ z hz, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hReG : ∀ z ∈ ball 0 R, (G z).re = Real.log ‖h z‖ - Real.log ‖κ‖ := by
    intro z hz
    rw [h_rep z hz, norm_mul, Complex.norm_exp,
      Real.log_mul (norm_ne_zero_iff.2 hκ_ne) (Real.exp_pos _).ne', Real.log_exp]
    ring
  -- `F - G` has constant real part, hence is constant
  have hG_diff : DifferentiableOn ℂ G (ball 0 R) :=
    fun z hz ↦ (hG z hz).differentiableAt.differentiableWithinAt
  have hG_an : AnalyticOnNhd ℂ G (ball 0 R) := hG_diff.analyticOnNhd isOpen_ball
  obtain ⟨c, hc⟩ := (hF_an.sub hG_an).eq_const_of_re_eq_const
    (c₀ := Real.log ‖κ‖)
    (fun z hz ↦ by
      simp only [Pi.sub_apply, Complex.sub_re]
      rw [hRe z hz, hReG z hz]
      ring)
    isOpen_ball ⟨⟨w, hw⟩, (convex_ball (0:ℂ) R).isPreconnected⟩
  -- Differentiate `F = G + c`
  have hEq : (fun z ↦ G z + c) =ᶠ[nhds w] F := by
    filter_upwards [isOpen_ball.mem_nhds hw] with z hz
    have h₄ := hc z hz
    simp only [Pi.sub_apply] at h₄
    linear_combination -h₄
  have hF_at := (hF_deriv w hw).congr_of_eventuallyEq hEq
  exact ((hG w hw).add_const c).unique hF_at

/-- Boundary special case of the differentiated Poisson representation: for `u` **on** the circle
and `w` inside, the circle average of `log ‖· - u‖` against the derived Herglotz–Riesz kernel is
`(w - u)⁻¹`. This provides the boundary-divisor correction in the differentiated Poisson–Jensen
formula. -/
theorem circleAverage_smul_log_norm_sub_sphere {u w : ℂ} {R : ℝ}
    (hu : u ∈ sphere (0 : ℂ) R) (hw : w ∈ ball (0 : ℂ) R) :
    circleAverage (fun ζ ↦ derivHerglotzRieszKernel w ζ • (Real.log ‖ζ - u‖ : ℂ)) 0 R
      = (w - u)⁻¹ := by
  have h₂ : AnalyticOnNhd ℂ (fun ζ : ℂ ↦ ζ - u) (ball 0 R) := by fun_prop
  have h₃ : ∀ z ∈ ball (0 : ℂ) R, z - u ≠ 0 := by
    intro z hz
    rw [sub_ne_zero]
    grind [mem_sphere, mem_ball]
  have h₁ : MeromorphicOn (fun ζ : ℂ ↦ ζ - u) (closedBall 0 R) := by fun_prop
  have hmain := h₁.logDeriv_eq_circleAverage h₂ h₃ hw
  have h₄ : HasDerivAt (fun ζ : ℂ ↦ ζ - u) 1 w := by
    simpa using (hasDerivAt_id w).sub_const u
  rw [← hmain, logDeriv_apply, h₄.deriv, one_div]
