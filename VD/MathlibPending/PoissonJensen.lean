/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.MathlibSubmitted.PoissonJensen

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
## The Poisson–Jensen Formula
-/

variable {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}


/-- **The Poisson–Jensen Formula.** If `f` is meromorphic on `closedBall c R` and has vanishing
order at an interior point `w ∈ ball c R`, then the logarithm of the norm of the trailing
coefficient of `f` at `w` equals a Herglotz–Riesz weighted circle average of `log ‖f ·‖`, corrected
by a finite sum over the divisor of `f`.

This generalises Jensen's formula `MeromorphicOn.circleAverage_log_norm` from the centre `c` to an
arbitrary interior point `w`. -/
theorem MeromorphicOn.log_norm_meromorphicTrailingCoeffAt
    (h₁f : MeromorphicOn f (closedBall c R)) (h₁w : w ∈ ball c R)
    (h₂w : meromorphicOrderAt f w = 0) :
    Real.log ‖meromorphicTrailingCoeffAt f w‖
      = circleAverage (re ∘ herglotzRieszKernel c w * (Real.log ‖f ·‖)) c R
        - ∑ᶠ i, (divisor f (ball c R) i) * Real.log ‖canonicalFactor R (i - c) (w - c)‖ := by
  -- Reduce to the centred case by translating `f` to `g z = f (z + c)`.
  let g := fun z ↦ f (z + c)
  have hfg : f = fun z ↦ g (z - c) := by simp [g]
  repeat rw [hfg]
  simp only
  have htc : meromorphicTrailingCoeffAt (fun z ↦ g (z - c)) w
      = meromorphicTrailingCoeffAt g (w - c) := by
    rw [← hfg]
    exact (meromorphicTrailingCoeffAt_fun_comp_add_const_eq_meromorphicTrailingCoeffAt
      (f := f) (c := c) (x := w)).symm
  rw [htc, MeromorphicOn.log_norm_meromorphicTrailingCoeffAt₀ (R := R)]
  · congr 1
    · simp only [← Real.circleAverage_map_add_const (c := c), Pi.mul_apply, comp_apply,
        add_sub_cancel_right]
      congr
      ext x
      exact (herglotzRieszKernel_add_const c w x).symm
    · -- Translate the finsum by `i ↦ i + c`: a zero of `f` at `i + c` corresponds to a
      -- zero of `g` at `i`, and the canonical factors match accordingly.
      apply finsum_eq_of_bijective (· + c) (Equiv.addRight c).bijective
      intro x
      simp only [add_sub_cancel_right, divisor_ball_fun_comp_add_const_eq_divisor_ball]
  · simpa [mem_ball_zero_iff] using (mem_ball_iff_norm.1 h₁w)
  · change meromorphicOrderAt (fun z ↦ f (z + c)) (w - c) = 0
    rwa [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
  · have hf : (fun z ↦ g (z - c)) = f := funext fun z ↦ by simp [g]
    rwa [← meromorphicOn_closedBall_fun_comp_sub_const_iff_meromorphicOn_closedBall (c := c), hf]
