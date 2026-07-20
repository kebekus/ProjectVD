/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.OpenMapping
import VD.MathlibSubmitted.CauchyIntegralDeriv
import VD.MathlibSubmitted.PoissonIntegralDeriv
import VD.MathlibPending.PoissonJensen

/-!
# Differentiated Poisson Representation — LLD work packages B4–B5

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §4.

Mathlib target: extend `Mathlib/Analysis/Complex/Poisson.lean` (B4) and
`Mathlib/Analysis/Complex/CanonicalDecomposition.lean` (B5).
Dependencies: `VD/LLD/CauchyIntegralDeriv.lean` (B1–B3) and the Poisson–Jensen chain
(`VD/MathlibSubmitted/BlaschkeDecomp2.lean`, `VD/MathlibPending/PoissonJensen.lean`).

- `MeromorphicOn.logDeriv_eq_circleAverage` (B4): if `h` is meromorphic on the closed ball,
  analytic and nonvanishing on the **open** ball, then its logarithmic derivative at interior
  points is the circle average of `log ‖h ·‖` against the `w`-derivative of the Herglotz–Riesz
  kernel. Proof: the kernel integral `F` is analytic in the pole with computable derivative
  (B1–B3); its real part is `log ‖h ·‖` by Poisson–Jensen; `logDeriv h` has a primitive `G` on
  the ball (`DifferentiableOn.isExactOn_ball`), so `h = κ · exp G`; then `F - G` has constant
  real part, hence is constant (`AnalyticOnNhd.eq_const_of_re_eq_const`), and differentiating
  gives the claim.

- `circleAverage_smul_log_norm_sub_sphere` (B4, boundary special case): since nonvanishing is
  required only on the *open* ball, the theorem applies to `h = (· - u)` with `u` **on the
  sphere**, yielding the boundary-divisor correction
  `circleAverage (fun ζ ↦ (2ζ/(ζ-w)²) • log ‖ζ - u‖) 0 R = (w - u)⁻¹` for free.

- `Complex.logDeriv_canonicalFactor`, `Complex.norm_logDeriv_canonicalFactor_le` (B5): the
  logarithmic derivative of the canonical factor is
  `-((w - a)⁻¹ + conj a / (R² - conj a * w))` away from the singularities, with the norm bound
  `‖logDeriv (canonicalFactor ρ a) w‖ ≤ ‖w - a‖⁻¹ + (ρ - r)⁻¹` on the circle `‖w‖ = r < ρ`.
-/

open Complex ComplexConjugate Filter Function MeromorphicOn Metric Real Set

/-!
## B5: The Logarithmic Derivative of the Canonical Factor
-/

namespace Complex

/-- The logarithmic derivative of the canonical factor, away from its zero and pole. -/
theorem logDeriv_canonicalFactor {R : ℝ} {a w : ℂ} (hR : R ≠ 0) (hw₁ : w ≠ a)
    (hw₂ : (R : ℂ) ^ 2 - conj a * w ≠ 0) :
    logDeriv (canonicalFactor R a) w
      = -((w - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * w)) := by
  have h₁ : HasDerivAt (fun z : ℂ ↦ (R : ℂ) ^ 2 - conj a * z) (-conj a) w := by
    simpa using ((hasDerivAt_id w).const_mul (conj a)).const_sub ((R : ℂ) ^ 2)
  have h₂ : HasDerivAt (fun z : ℂ ↦ (R : ℂ) * (z - a)) ((R : ℂ) * 1) w :=
    ((hasDerivAt_id w).sub_const a).const_mul _
  have h₃ : (R : ℂ) * (w - a) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 hR) (sub_ne_zero.2 hw₁)
  rw [canonicalFactor_def,
    logDeriv_div w hw₂ h₃ h₁.differentiableAt h₂.differentiableAt,
    logDeriv_const_mul w _ (Complex.ofReal_ne_zero.2 hR)]
  have h₄ : HasDerivAt (fun z : ℂ ↦ z - a) 1 w := by
    simpa using (hasDerivAt_id w).sub_const a
  rw [logDeriv_apply, logDeriv_apply, h₁.deriv, h₄.deriv]
  rw [neg_div]
  field_simp [sub_ne_zero.2 hw₁]
  ring

/--
Norm bound for the logarithmic derivative of the canonical factor on interior circles: for `‖a‖ < ρ`
and `‖w‖ = r < ρ`, we have `‖logDeriv (canonicalFactor ρ a) w‖ ≤ ‖w - a‖⁻¹ + (ρ - r)⁻¹`.
-/
theorem norm_logDeriv_canonicalFactor_le {ρ r : ℝ} {a w : ℂ}
    (ha : ‖a‖ < ρ) (hw : ‖w‖ = r) (hr : r < ρ) :
    ‖logDeriv (canonicalFactor ρ a) w‖ ≤ ‖w - a‖⁻¹ + (ρ - r)⁻¹ := by
  have hr₀ : 0 ≤ r := hw ▸ norm_nonneg w
  have hρ : 0 < ρ := lt_of_le_of_lt hr₀ hr
  rcases eq_or_ne w a with rfl | hw₁
  · rw [logDeriv_apply, canonicalFactor_apply_self, div_zero, norm_zero]
    exact add_nonneg (inv_nonneg.2 (norm_nonneg _)) (inv_nonneg.2 (by linarith))
  · have hw₂ : (ρ : ℂ) ^ 2 - conj a * w ≠ 0 := by
      intro hcon
      have h₁ : ‖((ρ : ℂ) ^ 2)‖ = ‖conj a * w‖ := by rw [sub_eq_zero.1 hcon]
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, norm_mul,
        Complex.norm_conj, hw] at h₁
      nlinarith
    rw [logDeriv_canonicalFactor hρ.ne' hw₁ hw₂, norm_neg]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_inv]
    gcongr
    -- ‖conj a / (ρ² - conj a * w)‖ ≤ (ρ - r)⁻¹
    rw [norm_div, Complex.norm_conj]
    have hD : ρ ^ 2 - ‖a‖ * r ≤ ‖(ρ : ℂ) ^ 2 - conj a * w‖ := by
      have h₁ := norm_sub_norm_le ((ρ : ℂ) ^ 2) (conj a * w)
      rwa [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, norm_mul,
        Complex.norm_conj, hw] at h₁
    have hD₀ : 0 < ρ ^ 2 - ‖a‖ * r := by nlinarith [norm_nonneg a]
    calc ‖a‖ / ‖(ρ : ℂ) ^ 2 - conj a * w‖
        ≤ ‖a‖ / (ρ ^ 2 - ‖a‖ * r) := by gcongr
      _ ≤ (ρ - r)⁻¹ := by
          rw [← one_div, div_le_div_iff₀ hD₀ (by linarith)]
          nlinarith [norm_nonneg a]

end Complex

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
      = circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖h ζ‖ : ℂ)) 0 R := by
  have hR : 0 < R := pos_of_mem_ball hw
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
    fun z hz ↦ hasDerivAt_circleAverage_herglotzRieszKernel_smul hgC hz
  have hF_an : AnalyticOnNhd ℂ F (ball 0 R) :=
    analyticOnNhd_circleAverage_herglotzRieszKernel_smul hgC
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
    rw [re_circleAverage_herglotzRieszKernel_smul hgR hz]
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
    circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖ζ - u‖ : ℂ)) 0 R = (w - u)⁻¹ := by
  have h₂ : AnalyticOnNhd ℂ (fun ζ : ℂ ↦ ζ - u) (ball 0 R) :=
    fun z _ ↦ analyticAt_id.sub analyticAt_const
  have h₃ : ∀ z ∈ ball (0 : ℂ) R, z - u ≠ 0 := by
    intro z hz
    apply sub_ne_zero.2
    intro hcon
    rw [mem_ball_zero_iff, hcon, mem_sphere_zero_iff_norm.1 hu] at hz
    exact lt_irrefl _ hz
  have h₁ : MeromorphicOn (fun ζ : ℂ ↦ ζ - u) (closedBall 0 R) :=
    fun z _ ↦ (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hmain := h₁.logDeriv_eq_circleAverage h₂ h₃ hw
  have h₄ : HasDerivAt (fun ζ : ℂ ↦ ζ - u) 1 w := by
    simpa using (hasDerivAt_id w).sub_const u
  rw [← hmain, logDeriv_apply, h₄.deriv, one_div]
