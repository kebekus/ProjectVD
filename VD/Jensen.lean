import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import VD.specialFunctions_CircleIntegral_affine
import VD.ToMathlib.TrailingCoefficientFactorizedRational

open Filter MeromorphicAt MeromorphicOn Metric Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
## Circle Averages

In preparation to the proof of Jensen's formula, compute several circle
integrals.
-/

/--
-/
@[simp]
lemma circleAverage_logAbs_affine {R : ℝ} {c u : ℂ} (hu : u ∈ closedBall c |R|) :
    circleAverage (log ‖· - u‖) c R = log R := by
  rw [← circleAverage_fun_add]
  have : (fun z ↦ log ‖z + c - u‖) = (log ‖· - (u - c)‖) := by
    ext z
    congr 2
    ring
  rw [this, int₅ (by aesop)]

@[simp]
lemma circleAverage_logAbs_factorizedRational {R : ℝ} {c : ℂ}
    (D : Function.locallyFinsuppWithin (closedBall c |R|) ℤ) :
    circleAverage (∑ᶠ u, ((D u) * log ‖· - u‖)) c R = ∑ᶠ u, (D u) * log R := by
  have h := D.finiteSupport (isCompact_closedBall c |R|)
  calc circleAverage (∑ᶠ u, ((D u) * log ‖· - u‖)) c R
  _ = circleAverage (∑ u ∈ h.toFinset, ((D u) * log ‖· - u‖)) c R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    contrapose
    aesop
  _ = ∑ i ∈ h.toFinset, circleAverage (fun x ↦ ↑(D i) * log ‖x - i‖) c R := by
    rw [circleAverage_sum]
    intro u hu
    apply IntervalIntegrable.const_mul
    apply circleIntegrable_log_norm_meromorphicOn (f := (· - u))
    apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn
  _ = ∑ u ∈ h.toFinset, ↑(D u) * log R := by
    apply Finset.sum_congr rfl
    intro u hu
    simp_rw [← smul_eq_mul, circleAverage_fun_smul]
    congr
    apply circleAverage_logAbs_affine
    apply D.supportWithinDomain
    simp_all
  _ = ∑ᶠ u, (D u) * log R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    aesop

-- WARNING: Want that for function to E
@[simp]
lemma circleAverage_nonVanishAnalytic {R : ℝ} {c : ℂ} {g : ℂ → ℂ}
    (h₁g : AnalyticOnNhd ℂ g (closedBall c |R|))
    (h₂g : ∀ u : closedBall c |R|, g u ≠ 0) :
    circleAverage (log ‖g ·‖) c R = log ‖g c‖ := by
  apply harmonic_meanValue₂
    (fun x hx ↦ logabs_of_holomorphicAt_is_harmonic (h₁g x hx).holomorphicAt (h₂g ⟨x, hx⟩))

/-!
## Jensen's Formula
-/

-- WARNING: Want that for function to E
theorem MeromorphicOn.JensenFormula {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0) (h₁f : MeromorphicOn f (closedBall 0 |R|)) :
    circleAverage (log ‖f ·‖) 0 R
      = ∑ᶠ u, divisor f (closedBall 0 |R|) u * log (R * ‖u‖⁻¹)
        + divisor f (closedBall 0 |R|) 0 * log R + log ‖meromorphicTrailingCoeffAt f 0‖ := by
  -- Shorthand notation to keep line size in check
  let CB := closedBall (0 : ℂ) |R|
  by_cases h₂f : ∀ u : CB, meromorphicOrderAt f u ≠ ⊤
  · have h₃f := (divisor f CB).finiteSupport (isCompact_closedBall 0 |R|)
    -- Extract zeros & poles and compute
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.extract_zeros_poles h₂f h₃f
    calc circleAverage (log ‖f ·‖) 0 R
    _ = circleAverage ((∑ᶠ u, (divisor f CB u * log ‖· - u‖)) + (log ‖g ·‖)) 0 R := by
      have h₄g := extract_zeros_poles_log h₂g h₃g
      rw [circleAverage_congr_codiscreteWithin (codiscreteWithin.mono sphere_subset_closedBall h₄g) hR]
    _ = circleAverage (∑ᶠ u, (divisor f CB u * log ‖· - u‖)) 0 R + circleAverage (log ‖g ·‖) 0 R := by
      apply circleAverage_add
      exact circleIntegrable_log_norm_factorizedRational (divisor f CB)
      exact circleIntegrable_log_norm_meromorphicOn (h₁g.mono sphere_subset_closedBall).meromorphicOn
    _ = ∑ᶠ u, divisor f CB u * log R + log ‖g 0‖ := by simp [h₁g, h₂g]
    _ = ∑ᶠ u, divisor f CB u * log R + (log ‖meromorphicTrailingCoeffAt f 0‖ - ∑ᶠ u, divisor f CB u * log ‖u‖) := by
      have t₀ : 0 ∈ CB := by simp [CB]
      have t₁ : AccPt 0 (𝓟 CB) := by
        apply accPt_iff_frequently_nhdsNE.mpr
        apply compl_notMem
        apply mem_nhdsWithin.mpr
        use ball 0 |R|
        simpa [hR] using fun _ ⟨h, _⟩ ↦ ball_subset_closedBall h
      simp [MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles_log h₃f t₀ t₁ (h₁f 0 t₀) (h₁g 0 t₀) (h₂g ⟨0, t₀⟩) h₃g]
    _ = ∑ᶠ u, divisor f CB u * log R - ∑ᶠ u, divisor f CB u * log ‖u‖ + log ‖meromorphicTrailingCoeffAt f 0‖ := by
      ring
    _ = (∑ᶠ u, divisor f CB u * (log R - log ‖u‖)) + log ‖meromorphicTrailingCoeffAt f 0‖ := by
      rw [← finsum_sub_distrib]
      simp_rw [← mul_sub]
      repeat apply h₃f.subset (fun _ ↦ (by simp_all))
    _ = ∑ᶠ u, divisor f CB u * log (R * ‖u‖⁻¹) + divisor f CB 0 * log R + log ‖meromorphicTrailingCoeffAt f 0‖ := by
      rw [Function.locallyFinsuppWithin.countingFunction_finsum_eq_finsum_add hR h₃f]
  · -- Trivial case: `f` vanishes on a codiscrete set
    rw [← h₁f.exists_meromorphicOrderAt_ne_top_iff_forall
      ⟨nonempty_closedBall.mpr (abs_nonneg R), (convex_closedBall 0 |R|).isPreconnected⟩] at h₂f
    push_neg at h₂f
    have : divisor f CB = 0 := by
      ext x
      by_cases h : x ∈ CB
      <;> simp_all [CB, divisor_def]
    simp only [CB, this, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero, zero_mul,
      finsum_zero, add_zero, zero_add]
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top (by aesop), norm_zero, log_zero]
    have : f =ᶠ[codiscreteWithin CB] 0 := by
      filter_upwards [h₁f.meromorphicNFAt_mem_codiscreteWithin, self_mem_codiscreteWithin CB]
        with z h₁z h₂z
      simpa [h₂f ⟨z, h₂z⟩] using (not_iff_not.2 h₁z.meromorphicOrderAt_eq_zero_iff)
    rw [circleAverage_congr_codiscreteWithin (f₂ := 0) _ hR]
    simp only [circleAverage, mul_inv_rev, Pi.zero_apply, intervalIntegral.integral_zero,
      smul_eq_mul, mul_zero]
    apply Filter.codiscreteWithin.mono (U := CB) sphere_subset_closedBall
    filter_upwards [this] with z hz
    simp_all
