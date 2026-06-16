/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.MathlibPending.PoissonJensen
import VD.MathlibSubmitted.BoundedRangeIsBigO
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic

/-!
# Boundedness of the Proximity Function

For an entire function `f : ℂ → ℂ`, the Nevanlinna proximity function `proximity f ⊤` (the circle
average of `log⁺ ‖f ·‖`) is `O(1)` along `atTop` if and only if `f` is constant. This is a
value-distribution-theoretic form of Liouville's theorem,
`ValueDistribution.proximity_isBigO_one_iff_exists_eq_const`.

The proof rests on a Poisson–Jensen estimate bounding `log ‖f w‖` by a fixed multiple of the
proximity function (the private lemmas `log_norm_le_circleAverage_posLog_norm` and
`log_norm_le_three_mul_proximity`), combined with Liouville's theorem.

Along the way this file also collects a few supporting results:
* lemmas on divisors and trailing coefficients of meromorphic functions;
* a lower bound for the norm of the canonical factor on the open ball.

The equivalences between bounded range and `IsBigO` asymptotics for functions `ℝ → ℝ` used in the
final argument live in `VD.MathlibSubmitted.BoundedRangeIsBigO`.
-/

open Asymptotics Bornology Complex ComplexConjugate Filter Function MeromorphicOn Metric Real Set
open scoped Topology

variable {f : ℂ → ℂ} {U : Set ℂ} {x z w : ℂ} {R : ℝ}

/-!
## Divisors and Trailing Coefficients
-/

/-- A meromorphic function whose order vanishes at `w` has trivial divisor at `w`. -/
@[simp] theorem divisor_eq_zero_of_meromorphicOrderAt_eq_zero
    (hf : meromorphicOrderAt f w = 0) :
    divisor f U w = 0 := by
  simp [divisor_def, hf]

/-- At a point where `f` is analytic and its order vanishes, the trailing coefficient of `f`
is just the value `f x`. -/
@[simp] lemma AnalyticAt.meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq_zero
    (h₁ : AnalyticAt ℂ f x) (h₂ : meromorphicOrderAt f x = 0) :
    meromorphicTrailingCoeffAt f x = f x := by
  apply h₁.meromorphicTrailingCoeffAt_of_ne_zero
  rwa [h₁.meromorphicOrderAt_eq, ENat.map_natCast_eq_zero, h₁.analyticOrderAt_eq_zero] at h₂

/-!
## The Canonical Factor on the Open Ball
-/

/-- The canonical factor `canonicalFactor R w` has norm strictly greater than one at every
point `z` of the open ball `ball 0 R` other than its pole `w`. -/
theorem one_lt_norm_canonicalFactor (hw : w ∈ ball 0 R) (hz : z ∈ ball 0 R) (hzw : z ≠ w) :
    1 < ‖canonicalFactor R w z‖ := by
  have h_norm : R * ‖z - w‖ < ‖R ^ 2 - conj w * z‖ := by
    simp_all only [mem_ball, dist_zero_right, norm_def, normSq, MonoidWithZeroHom.coe_mk,
      ZeroHom.coe_mk, ne_eq, sub_re, sub_im, mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add,
      mul_im]
    rw [Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg _) hw)] at *
    apply Real.lt_sqrt_of_sq_lt
    norm_cast
    rw [mul_pow, Real.sq_sqrt (by nlinarith)]
    nlinarith
  have hR : 0 < R := pos_of_mem_ball hw
  simp_all only [mem_ball, dist_zero_right, ne_eq,
    canonicalFactor, Complex.norm_div, Complex.norm_mul, norm_real, norm_eq_abs, gt_iff_lt]
  rwa [one_lt_div (mul_pos (abs_pos.mpr hR.ne') (norm_pos_iff.mpr (sub_ne_zero.mpr hzw))),
    abs_of_pos hR]

/-!
## Boundedness of the Proximity Function

The technical estimates `log_norm_le_circleAverage_posLog_norm` and
`log_norm_le_three_mul_proximity` are auxiliary to the main results and are kept `private`.
-/

namespace ValueDistribution

/-- Poisson–Jensen estimate: if `f` is analytic on `closedBall 0 R` and its order vanishes
at `w ∈ ball 0 R`, then `log ‖f w‖` is bounded by `(R + ‖w‖) / (R - ‖w‖)` times the circle
average of `log⁺ ‖f‖`. -/
private theorem log_norm_le_circleAverage_posLog_norm
    (h₁w : w ∈ ball 0 R) (h₂w : meromorphicOrderAt f w = 0)
    (h₁f : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    Real.log ‖f w‖ ≤ ((R + ‖w‖) / (R - ‖w‖)) * circleAverage (log⁺ ‖f ·‖) 0 R := by
  have h₂f : (divisor f (ball 0 R)).support.Finite := by
    apply ((divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
    intro b hb
    rw [mem_support, ne_eq, divisor_apply (fun x hx ↦ (h₁f x hx).meromorphicAt)
      (ball_subset_closedBall ((divisor f (ball 0 R)).supportWithinDomain hb))]
    rwa [mem_support, ne_eq, divisor_apply
      (fun c hc ↦ (fun x hx ↦ (h₁f x hx).meromorphicAt) c (ball_subset_closedBall hc))
      ((divisor f (ball 0 R)).supportWithinDomain hb)] at hb
  have h₃f : MeromorphicOn f (sphere 0 |R|) := by
    rw [abs_of_pos (pos_of_mem_ball h₁w)]
    exact fun x hx ↦ (h₁f x (sphere_subset_closedBall hx)).meromorphicAt
  calc Real.log ‖f w‖
    _ = Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
      rw [AnalyticAt.meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq_zero
        (h₁f w (ball_subset_closedBall h₁w)) h₂w]
    _ ≤ circleAverage (re ∘ herglotzRieszKernel 0 w * (Real.log ‖f ·‖)) 0 R := by
      rw [MeromorphicOn.log_norm_meromorphicTrailingCoeffAt
        (fun x hx ↦ (h₁f x hx).meromorphicAt) h₁w h₂w]
      simp only [sub_zero]
      apply sub_le_self
      rw [finsum_eq_sum_of_support_subset (s := h₂f.toFinset) _ (fun _ _ ↦ by aesop)]
      refine Finset.sum_nonneg fun i hi ↦ mul_nonneg ?_ ?_
      · exact_mod_cast (h₁f.mono ball_subset_closedBall).divisor_nonneg i
      · have := (divisor f (ball 0 R)).supportWithinDomain
        exact log_nonneg (one_lt_norm_canonicalFactor (by aesop) h₁w (by aesop)).le
    _ ≤ circleAverage (re ∘ herglotzRieszKernel 0 w * (log⁺ ‖f ·‖)) 0 R := by
      apply circleAverage_mono ((circleIntegrable_log_norm h₃f).mul_of_continuousOn
        (continuousOn_herglotzRieszKernel_sphere h₁w)) ((circleIntegrable_posLog_norm
        h₃f).mul_of_continuousOn (continuousOn_herglotzRieszKernel_sphere h₁w))
      intro x hx
      simp only [Pi.mul_apply, comp_apply]
      gcongr
      · trans (R - ‖w - 0‖) / (R + ‖w - 0‖)
        · rw [sub_zero]
          simp only [mem_ball, dist_zero_right] at h₁w
          exact div_nonneg (sub_nonneg.2 h₁w.le)
            (add_nonneg ((norm_nonneg w).trans h₁w.le) (norm_nonneg w))
        · apply le_re_herglotzRieszKernel _ h₁w
          rwa [abs_of_pos (pos_of_mem_ball h₁w)] at hx
      · rw [posLog_apply]
        exact le_max_right _ _
    _ ≤ circleAverage (((R + ‖w‖) / (R - ‖w‖)) • (log⁺ ‖f ·‖)) 0 R := by
      have hint : CircleIntegrable (log⁺ ‖f ·‖) 0 R := circleIntegrable_posLog_norm h₃f
      apply circleAverage_mono (hint.re_herglotzRieszKernel_smul h₁w)
        (hint.mul_of_continuousOn (by fun_prop))
      intro x hx
      rw [abs_of_pos (pos_of_mem_ball h₁w)] at hx
      rw [Pi.smul_apply', comp_apply, smul_eq_mul, Pi.mul_apply]
      gcongr
      · exact posLog_nonneg
      · simpa [herglotzRieszKernel] using re_herglotzRieszKernel_le hx h₁w
    _ = ((R + ‖w‖) / (R - ‖w‖)) * circleAverage (log⁺ ‖f ·‖) 0 R := circleAverage_smul

/-- For an entire function `f`, `log ‖f w‖` is bounded by three times the proximity function
evaluated at `‖2 * w‖`. -/
private theorem log_norm_le_three_mul_proximity (h₁f : AnalyticOnNhd ℂ f univ) :
    Real.log ‖f w‖ ≤ 3 * proximity f ⊤ ‖2 * w‖ := by
  by_cases hfw : f w = 0
  · simp only [hfw, norm_zero, Real.log_zero, Complex.norm_mul, Complex.norm_ofNat, Nat.ofNat_pos,
      mul_nonneg_iff_of_pos_left]
    apply proximity_nonneg
  rw [proximity_top]
  by_cases hw : w = 0
  · simp only [hw, mul_zero, norm_zero, circleAverage_zero]
    rw [← one_mul (a := Real.log ‖f 0‖), mul_comm, mul_comm (a := 3)]
    gcongr
    · exact posLog_nonneg
    · simp [posLog]
    · norm_num
  have hwmem : w ∈ ball 0 (2 * ‖w‖) := by aesop
  have hord : meromorphicOrderAt f w = 0 := by
    have hmem := h₁f w (mem_univ w)
    rw [hmem.meromorphicOrderAt_eq, ENat.map_natCast_eq_zero, hmem.analyticOrderAt_eq_zero]
    exact hfw
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have h₁f' : AnalyticOnNhd ℂ f (closedBall 0 (2 * ‖w‖)) := h₁f.mono (by tauto)
  convert log_norm_le_circleAverage_posLog_norm hwmem hord h₁f' using 2
  · field_simp
    ring
  · simp

/--
If a function is eventually constant on a codiscrete subset of `ℂ`, then its proximity function is
`O(1)` at `atTop`.
-/
theorem proximity_isBigO_one_of_eventuallyConst {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (h : EventuallyConst f (codiscrete ℂ)) :
    proximity f ⊤ =O[atTop] (1 : ℝ → ℝ) := by
  rw [eventuallyConst_iff_exists_eventuallyEq] at h
  obtain ⟨c, hc⟩ := h
  simp_rw [isBigO_iff, eventually_atTop]
  exact ⟨log⁺ ‖c‖, 1, fun _ _ ↦ by
    simp [proximity_congr_codiscrete hc (by linarith), abs_of_nonneg posLog_nonneg]⟩

/--
An entire function `ℂ → ℂ` has bounded proximity function if and only if it is constant. This is a
value distribution-theoretic form of Liouville's theorem.
-/
theorem proximity_isBigO_one_iff_exists_eq_const (h₁f : AnalyticOnNhd ℂ f univ) :
    proximity f ⊤ =O[atTop] (1 : ℝ → ℝ) ↔ ∃ c, f = fun _ ↦ c := by
  have hcont : Continuous f := h₁f.continuous
  constructor
  · intro h
    rw [← Continuous.isBounded_range_iff_isBigO_atTop_of_even (by fun_prop) proximity_even] at h
    have hbdd : IsBounded (range f) := by
      rw [isBounded_iff_forall_norm_le] at h ⊢
      obtain ⟨C, hC⟩ := h
      refine ⟨exp (3 * C), ?_⟩
      rintro _ ⟨y, rfl⟩
      by_cases hy : f y = 0
      · rw [hy, norm_zero]
        positivity
      rw [← Real.log_le_log_iff (norm_pos_iff.2 hy) (Real.exp_pos _), Real.log_exp]
      calc Real.log ‖f y‖
        _ ≤ 3 * proximity f ⊤ ‖2 * y‖ := log_norm_le_three_mul_proximity h₁f
        _ ≤ 3 * C := by
          have hmem := hC (proximity f ⊤ ‖2 * y‖) ⟨‖2 * y‖, rfl⟩
          rw [Real.norm_of_nonneg (proximity_nonneg ‖2 * y‖)] at hmem
          linarith
    have hdiff : Differentiable ℂ f := fun x ↦ (h₁f x (mem_univ x)).differentiableAt
    exact ⟨f 0, funext fun x ↦ hdiff.apply_eq_apply_of_bounded hbdd x 0⟩
  · rintro ⟨c, hc⟩
    rw [hc, show proximity (fun _ ↦ c) ⊤ = fun _ ↦ log⁺ ‖c‖ from funext fun _ ↦ proximity_const]
    exact isBigO_const_const _ one_ne_zero atTop

end ValueDistribution
