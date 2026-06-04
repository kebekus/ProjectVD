import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.JensenFormula
import VD.MathlibSubmitted.BlaschkeDecomp2
import VD.MathlibPending.BlaschkeDecomp3

open Complex Filter Function MeromorphicOn Metric Real Set Classical Topology --ValueDistribution

/-!
## Additional Material
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticOnNhd_herglotzRieszKernel_compl {c w : ℂ} :
    AnalyticOnNhd ℂ (herglotzRieszKernel c w) {w}ᶜ := by
  intro x hx
  unfold herglotzRieszKernel
  have : x - w ≠ 0 := by grind
  fun_prop (disch := aesop)

@[fun_prop]
theorem continuousOn_herglotzRieszKernel_sphere {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R):
    ContinuousOn (re ∘ herglotzRieszKernel c w) (sphere c |R|) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.comp (by fun_prop) (analyticOnNhd_herglotzRieszKernel_compl x _).continuousAt
  by_contra h
  simp only [mem_compl_iff, mem_singleton_iff, not_not] at h
  rw [← h, ← abs_of_pos (pos_of_mem_ball hw), mem_ball_iff_norm] at hw
  simp_all

theorem CircleIntegrable.circleIntegrable_re_herglotzRieszKernel_smul {c w : ℂ} {R : ℝ} {f : ℂ → E}
    (hw : w ∈ ball c R)
    (hf : CircleIntegrable f c R) :
    CircleIntegrable (re ∘ herglotzRieszKernel c w • f) c R := by
  apply hf.smul_of_continuousOn (by fun_prop)

/-!
## Formula goes here
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {x c w : ℂ} {f h : ℂ → ℂ}

set_option backward.isDefEq.respectTransparency false in
lemma xx
    {f h : ℂ → ℂ}
    (hw : w ∈ ball 0 R)
    (h₀f : MeromorphicOn f (closedBall 0 R)) -- can be deduced
    (h₁h : AnalyticOnNhd ℂ h (closedBall 0 R))
    (h₂h : ∀ u ∈ (closedBall 0 R), h u ≠ 0)
    (h₁f : f =ᶠ[codiscreteWithin (closedBall 0 R)]
      ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
        * (∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h) :
    circleAverage (re ∘ herglotzRieszKernel 0 w * (Real.log ‖f ·‖)) 0 R =
        ∑ᶠ x, (divisor f (sphere 0 R)) x * Real.log ‖w - x‖ + Real.log ‖h w‖ := by
  -- Facts used in the calculation below
  have hR : 0 < R := pos_of_mem_ball hw
  have h₂f : (divisor f (sphere 0 R)).support.Finite := divisor_sphere_support_finite
  have h₃f : (divisor f (ball 0 R)).support.Finite := h₀f.divisor_ball_support_finite
  have h₄f {a : ℂ} (ha : (divisor f (sphere 0 R)) a = 0) : ∀ b ∈ h₂f.toFinset, ‖a - b‖ ^ (divisor f (sphere 0 R)) b ≠ 0 := by
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
  -- Regularity properties of functions used in the calculation below
  have ρ₂ : CircleIntegrable (Complex.re ∘ herglotzRieszKernel 0 w • (Real.log ‖h ·‖)) 0 R := by
    apply CircleIntegrable.circleIntegrable_re_herglotzRieszKernel_smul hw
    apply circleIntegrable_log_norm (h₁h.meromorphicOn.mono_set _)
    simpa [abs_of_pos (pos_of_mem_ball hw)] using sphere_subset_closedBall
  have ρ₃ : ∀ i ∈ h₂f.toFinset, CircleIntegrable ((divisor f (sphere 0 R)) i • re ∘ herglotzRieszKernel 0 w • (Real.log ‖· - i‖)) 0 R := by
    intro i hi
    rw [cast_smul]
    apply CircleIntegrable.const_smul
    apply CircleIntegrable.circleIntegrable_re_herglotzRieszKernel_smul hw
    apply circleIntegrable_log_norm (fun x hx ↦ by fun_prop)
  -- Proof of the main claim by calculation
  calc circleAverage (re ∘ herglotzRieszKernel 0 w • (Real.log ‖f ·‖)) 0 R
    _ = circleAverage (re ∘ herglotzRieszKernel 0 w •
        (Real.log ‖(((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
          * (∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h) ·‖)) 0 R := by
      apply circleAverage_congr_codiscreteWithin _ hR.ne'
      rw [abs_of_pos hR]
      filter_upwards [h₁f.filter_mono (codiscreteWithin_mono sphere_subset_closedBall)]
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
      simp [norm_canonicalFactor_eval_circle_eq_one ((divisor f (ball 0 R)).supportWithinDomain (h₃f.mem_toFinset.1 hb)) ha]
    _ = circleAverage (re ∘ herglotzRieszKernel 0 w • fun x ↦
        ∑ u ∈ h₂f.toFinset, (divisor f (sphere 0 R) u) * Real.log ‖x - u‖ + Real.log ‖h x‖) 0 R:= by
      apply circleAverage_congr_codiscreteWithin _ hR.ne'
      rw [abs_of_pos (pos_of_mem_ball hw)]
      filter_upwards [(divisor f (sphere 0 R)).eq_zero_codiscreteWithin,
        Filter.self_mem_codiscreteWithin (sphere 0 R)] with a ha h₂a
      simp only [Pi.smul_apply', smul_eq_mul, Complex.norm_mul, comp_apply, mul_eq_mul_left_iff]
      left
      rw [finprod_eq_prod_of_mulSupport_subset (s := h₂f.toFinset) _ (by aesop)]
      simp only [Finset.prod_apply, Pi.pow_apply, norm_prod, norm_zpow]
      rw [Real.log_mul (Finset.prod_ne_zero_iff.2 (h₄f ha)) (by simp [h₂h a (Std.le_of_eq h₂a)]), Real.log_prod (h₄f ha)]
      congr 1
      exact Finset.sum_congr rfl (fun i hi ↦ log_zpow ‖a - i‖ ((divisor f (sphere 0 R)) i))
    _ = circleAverage ( (∑ u ∈ h₂f.toFinset, (divisor f (sphere 0 R) u) • re ∘ herglotzRieszKernel 0 w • (Real.log ‖· - u‖))
          + re ∘ herglotzRieszKernel 0 w • (Real.log ‖h ·‖) ) 0 R := by
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
          (fun x hx ↦ (h₁h x hx).harmonicAt_log_norm (h₂h x hx)) hw,
        finsum_eq_sum_of_support_subset (s := h₂f.toFinset) _ (fun _ _ ↦ (by aesop))]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      rw [cast_smul, circleAverage_smul, smul_eq_mul, smul_eq_mul,
        circleAverage_re_herglotzRieszKernel_mul_log
          ((divisor f (sphere 0 R)).supportWithinDomain (h₂f.mem_toFinset.1 hx)) hw]

theorem poissonJensen₀
    (h₁w : w ∈ ball 0 R)
    (h₃w : meromorphicOrderAt f w = 0)
    (h₁f : MeromorphicOn f (closedBall 0 R)) :
    Real.log ‖meromorphicTrailingCoeffAt f w‖
      = circleAverage (re ∘ herglotzRieszKernel 0 w * (Real.log ‖f ·‖)) 0 R
        - ∑ᶠ i, (divisor f (ball 0 R) i) * Real.log ‖canonicalFactor R i w‖ := by
  have h₂w : w ∈ closedBall 0 R := ball_subset_closedBall h₁w
  have h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤ := by
    apply (h₁f.exists_meromorphicOrderAt_ne_top_iff_forall
      (isConnected_closedBall (pos_of_mem_ball h₁w).le)).1
    aesop
  obtain ⟨h, h₀h⟩ := h₁f.exists_ecanonicalDecomp h₂f
  have h₁h := h₀h.analyticOnNhd
  have h₂h := h₀h.ne_zero
  have h₃h := h₀h.eventuallyEq
  rw [xx h₁w h₁f h₁h h₂h h₃h]
  rw [h₀h.log_norm_eq h₂w h₃w (pos_of_mem_ball h₁w)]
  ring_nf
