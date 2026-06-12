/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.JensenFormula
import VD.MathlibSubmitted.BlaschkeDecomp2
import VD.MathlibPending.BlaschkeDecomp3
import VD.MathlibSubmitted.Translation

/-!
# The Poisson–Jensen Formula

This file establishes the **Poisson–Jensen formula**
`MeromorphicOn.log_norm_meromorphicTrailingCoeffAt`: for a function `f` that is meromorphic on the
closed ball `closedBall c R` and has vanishing order at an interior point `w`, the logarithm of the
norm of the trailing coefficient `meromorphicTrailingCoeffAt f w` is expressed as a Herglotz–Riesz
weighted circle average of `log ‖f ·‖`, corrected by a finite sum over the divisor of `f`.

The formula generalises Jensen's formula (`MeromorphicOn.circleAverage_log_norm`) from the centre
`c` to an arbitrary interior point `w`, the Herglotz–Riesz kernel `herglotzRieszKernel c w` playing
the role of the Poisson kernel.

The file also collects analytic and integrability properties of the Herglotz–Riesz kernel that are
needed along the way.
-/

open Complex Filter Function MeromorphicOn Metric Real Set Topology

/-!
## Analytic and Integrability Properties of the Herglotz–Riesz Kernel
-/

/-- The Herglotz–Riesz kernel `herglotzRieszKernel c w` is analytic away from its pole at `w`. -/
theorem analyticOnNhd_herglotzRieszKernel_compl {c w : ℂ} :
    AnalyticOnNhd ℂ (herglotzRieszKernel c w) {w}ᶜ := by
  intro x hx
  unfold herglotzRieszKernel
  have : x - w ≠ 0 := by grind
  fun_prop (disch := aesop)

/-- The real part of the Herglotz–Riesz kernel `herglotzRieszKernel c w` is continuous on the sphere
`sphere c |R|` around an interior point `w ∈ ball c R`. -/
@[fun_prop]
theorem continuousOn_herglotzRieszKernel_sphere {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    ContinuousOn (re ∘ herglotzRieszKernel c w) (sphere c |R|) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.comp (by fun_prop) (analyticOnNhd_herglotzRieszKernel_compl x _).continuousAt
  by_contra h
  simp only [mem_compl_iff, mem_singleton_iff, not_not] at h
  rw [← h, ← abs_of_pos (pos_of_mem_ball hw), mem_ball_iff_norm] at hw
  simp_all

/-- Scaling a circle-integrable function by the real part of the Herglotz–Riesz kernel preserves
circle integrability. -/
theorem CircleIntegrable.re_herglotzRieszKernel_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {c w : ℂ} {R : ℝ} {f : ℂ → E} (hw : w ∈ ball c R)
    (hf : CircleIntegrable f c R) :
    CircleIntegrable (re ∘ herglotzRieszKernel c w • f) c R :=
  hf.smul_of_continuousOn (by fun_prop)

/-!
## The Poisson–Jensen Formula
-/

variable {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}

/-
The Poisson–Jensen formula in the special case where the disc is centred at the origin. This is an
auxiliary result; the general statement is `MeromorphicOn.log_norm_meromorphicTrailingCoeffAt`.
-/
private theorem poissonJensen₀ (h₁w : w ∈ ball 0 R) (h₃w : meromorphicOrderAt f w = 0)
    (h₁f : MeromorphicOn f (closedBall 0 R)) :
    Real.log ‖meromorphicTrailingCoeffAt f w‖
      = circleAverage (re ∘ herglotzRieszKernel 0 w * (Real.log ‖f ·‖)) 0 R
        - ∑ᶠ i, (divisor f (ball 0 R) i) * Real.log ‖canonicalFactor R i w‖ := by
  have hR : 0 < R := pos_of_mem_ball h₁w
  have h₂w : w ∈ closedBall 0 R := ball_subset_closedBall h₁w
  -- Write `f = (Blaschke product) • h` with `h` analytic and nowhere zero on the closed
  -- ball, where the Blaschke product collects the zeros and poles of `f`.
  obtain ⟨h, h₀h⟩ := h₁f.exists_ecanonicalDecomp <| by
    apply (h₁f.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_closedBall hR.le)).1
    aesop
  have h₁h := h₀h.analyticOnNhd
  have h₂h := h₀h.ne_zero
  have h₃h := h₀h.eventuallyEq
  -- Auxiliary finiteness and integrability facts for the boundary computation below.
  have h₂f : (divisor f (sphere 0 R)).support.Finite := divisor_sphere_support_finite
  have h₃f : (divisor f (ball 0 R)).support.Finite := h₁f.divisor_ball_support_finite
  have h₄f {a : ℂ} (ha : (divisor f (sphere 0 R)) a = 0) :
      ∀ b ∈ h₂f.toFinset, ‖a - b‖ ^ (divisor f (sphere 0 R)) b ≠ 0 := by
    intro b hb
    apply zpow_ne_zero
    rw [ne_eq, norm_eq_zero]
    by_contra hCon
    rw [sub_eq_zero] at hCon
    subst hCon
    rw [Finite.mem_toFinset, mem_support, ne_eq] at hb
    tauto
  have cast_smul {x : ℂ} {φ : ℂ → ℝ} :
      (divisor f (sphere 0 R)) x • φ = ((divisor f (sphere 0 R)) x : ℝ) • φ := by aesop
  have ρ₂ : CircleIntegrable (Complex.re ∘ herglotzRieszKernel 0 w • (Real.log ‖h ·‖)) 0 R := by
    apply CircleIntegrable.re_herglotzRieszKernel_smul h₁w
    apply circleIntegrable_log_norm (h₁h.meromorphicOn.mono_set _)
    simpa [abs_of_pos hR] using sphere_subset_closedBall
  have ρ₃ : ∀ i ∈ h₂f.toFinset, CircleIntegrable ((divisor f (sphere 0 R)) i •
      re ∘ herglotzRieszKernel 0 w • (Real.log ‖· - i‖)) 0 R := by
    intro i hi
    rw [cast_smul]
    apply CircleIntegrable.const_smul
    apply CircleIntegrable.re_herglotzRieszKernel_smul h₁w
    apply circleIntegrable_log_norm (fun x hx ↦ by fun_prop)
  -- The Poisson–Jensen identity for the circle average of `log ‖f‖`, obtained by
  -- replacing `f` with its canonical decomposition and integrating term by term.
  have key : circleAverage (re ∘ herglotzRieszKernel 0 w • (Real.log ‖f ·‖)) 0 R =
      ∑ᶠ x, (divisor f (sphere 0 R)) x * Real.log ‖w - x‖ + Real.log ‖h w‖ :=
    calc circleAverage (re ∘ herglotzRieszKernel 0 w • (Real.log ‖f ·‖)) 0 R
      _ = circleAverage (re ∘ herglotzRieszKernel 0 w •
          (Real.log ‖(((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
            * (∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h) ·‖)) 0 R := by
        apply circleAverage_congr_codiscreteWithin _ hR.ne'
        rw [abs_of_pos hR]
        filter_upwards [h₃h.filter_mono (codiscreteWithin_mono sphere_subset_closedBall)]
        simp_all
      _ = circleAverage (re ∘ herglotzRieszKernel 0 w •
          (Real.log ‖(((∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h) ·‖)) 0 R := by
        apply circleAverage_congr_sphere
        rw [abs_of_pos hR]
        intro a ha
        simp only [Pi.smul_apply', Pi.mul_apply, comp_apply, norm_smul, norm_smul, norm_mul]
        congr
        convert one_mul (a := ‖(∏ᶠ (u : ℂ), (· - u) ^ (divisor f (sphere 0 R)) u) a‖)
        rw [finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _ (by aesop)]
        simp only [zpow_neg, Finset.prod_apply, Pi.inv_apply, Pi.pow_apply, Finset.prod_inv_distrib,
          norm_inv, norm_prod, norm_zpow, inv_eq_one]
        apply Finset.prod_eq_one
        intro b hb
        simp [norm_canonicalFactor_eval_circle_eq_one
          ((divisor f (ball 0 R)).supportWithinDomain (h₃f.mem_toFinset.1 hb)) ha]
      _ = circleAverage (re ∘ herglotzRieszKernel 0 w • fun x ↦
          ∑ u ∈ h₂f.toFinset, (divisor f (sphere 0 R) u) * Real.log ‖x - u‖
            + Real.log ‖h x‖) 0 R := by
        apply circleAverage_congr_codiscreteWithin _ hR.ne'
        rw [abs_of_pos hR]
        filter_upwards [(divisor f (sphere 0 R)).eq_zero_codiscreteWithin,
          Filter.self_mem_codiscreteWithin (sphere 0 R)] with a ha h₂a
        simp only [Pi.smul_apply', smul_eq_mul, Complex.norm_mul, comp_apply, mul_eq_mul_left_iff]
        left
        rw [finprod_eq_prod_of_mulSupport_subset (s := h₂f.toFinset) _ (by aesop)]
        simp only [Finset.prod_apply, Pi.pow_apply, norm_prod, norm_zpow]
        rw [Real.log_mul (Finset.prod_ne_zero_iff.2 (h₄f ha))
            (by simp [h₂h a (Std.le_of_eq h₂a)]), Real.log_prod (h₄f ha)]
        congr 1
        exact Finset.sum_congr rfl (fun i hi ↦ log_zpow ‖a - i‖ ((divisor f (sphere 0 R)) i))
      _ = circleAverage ((∑ u ∈ h₂f.toFinset,
              (divisor f (sphere 0 R) u) • re ∘ herglotzRieszKernel 0 w • (Real.log ‖· - u‖))
            + re ∘ herglotzRieszKernel 0 w • (Real.log ‖h ·‖)) 0 R := by
        apply circleAverage_congr_sphere
        intro b hb
        simp only [Pi.smul_apply', comp_apply, smul_eq_mul, zsmul_eq_mul, Pi.add_apply,
          Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply, mul_add, Finset.mul_sum]
        congr
        ext
        ring
      _ = ∑ᶠ (x : ℂ), (divisor f (sphere 0 R)) x * Real.log ‖w - x‖ + Real.log ‖h w‖ := by
        rw [circleAverage_add (CircleIntegrable.sum _ ρ₃) ρ₂, circleAverage_sum ρ₃,
          InnerProductSpace.HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
            (fun x hx ↦ (h₁h x hx).harmonicAt_log_norm (h₂h x hx)) h₁w,
          finsum_eq_sum_of_support_subset (s := h₂f.toFinset) _ (fun _ _ ↦ (by aesop))]
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        rw [cast_smul, circleAverage_smul, smul_eq_mul, smul_eq_mul,
          circleAverage_re_herglotzRieszKernel_mul_log
            ((divisor f (sphere 0 R)).supportWithinDomain (h₂f.mem_toFinset.1 hx)) h₁w]
  -- Combine the circle-average identity with the value of `log ‖f‖` at `w`.
  rw [show (re ∘ herglotzRieszKernel 0 w * (Real.log ‖f ·‖))
        = re ∘ herglotzRieszKernel 0 w • (Real.log ‖f ·‖) by ext x; simp [smul_eq_mul], key,
    h₀h.log_norm_eq h₂w h₃w hR]
  ring_nf

/-- **The Poisson–Jensen Formula.** If `f` is meromorphic on `closedBall c R` and has vanishing
order at an interior point `w ∈ ball c R`, then the logarithm of the norm of the trailing
coefficient of `f` at `w` equals a Herglotz–Riesz weighted circle average of `log ‖f ·‖`, corrected
by a finite sum over the divisor of `f`.

This generalises Jensen's formula `MeromorphicOn.circleAverage_log_norm` from the centre `c` to an
arbitrary interior point `w`. -/
theorem MeromorphicOn.log_norm_meromorphicTrailingCoeffAt
    (h₁f : MeromorphicOn f (closedBall c R)) (h₁w : w ∈ ball c R)
    (h₃w : meromorphicOrderAt f w = 0) :
    Real.log ‖meromorphicTrailingCoeffAt f w‖
      = circleAverage (re ∘ herglotzRieszKernel c w * (Real.log ‖f ·‖)) c R
        - ∑ᶠ i, (divisor f (ball c R) i) * Real.log ‖canonicalFactor R (i - c) (w - c)‖ := by
  -- Reduce to the centred case by translating `f` to `g z = f (z + c)`.
  let g := fun z ↦ f (z + c)
  have : f = fun z ↦ g (z - c) := by simp [g]
  repeat rw [this]
  simp only
  have : meromorphicTrailingCoeffAt (fun z ↦ g (z - c)) w
      = meromorphicTrailingCoeffAt g (w - c) := by
    rw [← this]
    exact (meromorphicTrailingCoeffAt_fun_comp_add_const_eq_meromorphicTrailingCoeffAt
      (f := f) (c := c) (x := w)).symm
  rw [this, poissonJensen₀ (R := R)]
  · congr 1
    · simp only [← Real.circleAverage_map_add_const (c := c), Pi.mul_apply, comp_apply,
        add_sub_cancel_right]
      congr
      ext x
      exact (herglotzRieszKernel_add_const c w x).symm
    · -- Translate the finsum by `i ↦ i + c`: a zero of `f` at `i + c` corresponds to a
      -- zero of `g` at `i`, and the canonical factors match accordingly.
      apply finsum_eq_of_bijective (fun i ↦ i + c) (Equiv.addRight c).bijective
      intro x
      simp only [add_sub_cancel_right, divisor_ball_fun_comp_add_const_eq_divisor_ball]
  · rw [mem_ball_iff_norm] at h₁w
    simpa [mem_ball_zero_iff] using h₁w
  · change meromorphicOrderAt (fun z ↦ f (z + c)) (w - c) = 0
    rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
    exact h₃w
  · have hf : (fun z ↦ g (z - c)) = f := funext fun z ↦ by simp [g]
    rw [← meromorphicOn_closedBall_fun_comp_sub_const_iff_meromorphicOn_closedBall (c := c), hf]
    exact h₁f
