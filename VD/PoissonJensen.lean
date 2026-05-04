import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.JensenFormula

open Complex Filter Function MeromorphicOn Metric Real Set Classical Topology --ValueDistribution

/-!
## Additional Material
-/

@[fun_prop]
lemma meromorphicAt_canonicalFactor {R : ℝ} {x w : ℂ} : MeromorphicAt (canonicalFactor R w) x := by
  rw [canonicalFactor_def]
  fun_prop

theorem meromorphicNFAt_comp_iff_of_deriv_ne_zero {x : ℂ} {f g : ℂ → ℂ} (hg : AnalyticAt ℂ g x) (hg' : deriv g x ≠ 0) :
    MeromorphicNFAt (f ∘ g) x ↔ MeromorphicNFAt f (g x) := by
  simp [meromorphicNFAt_iff_analyticAt_or, analyticAt_comp_iff_of_deriv_ne_zero hg hg',
    meromorphicAt_comp_iff_of_deriv_ne_zero hg hg',
    meromorphicOrderAt_comp_of_deriv_ne_zero hg hg']

theorem finprod_ne_zero {ι : Type*} {M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
  {f : ι → M₀} (h : ∀ i, f i ≠ 0) :
    ∏ᶠ i, f i ≠ 0 := by
  by_cases h₂ : Set.Finite f.mulSupport
  · grind [finprod_eq_prod f h₂, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

theorem MeromorphicOn.codiscreteWithin_setOf_meromorphicOrderAt_eq_zero_or_top {U : Set ℂ} {f : ℂ → ℂ}
    (h₁f : MeromorphicOn f U)
    (h₂f : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤) :
    {u ∈ U | meromorphicOrderAt f u = 0 ∨ meromorphicOrderAt f u = ⊤} ∈ codiscreteWithin U := by
  convert mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
    h₁f.codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top
  aesop

theorem MeromorphicOn.codiscreteWithin_setOf_ne_zero {U : Set ℂ} {f : ℂ → ℂ}
    (h₁f : MeromorphicOn f U)
    (h₂f : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤) :
    ∀ᶠ x in codiscreteWithin U, f x ≠ 0 := by
  filter_upwards [h₁f.analyticAt_mem_codiscreteWithin,
    h₁f.codiscreteWithin_setOf_meromorphicOrderAt_eq_zero_or_top h₂f] with x h₁x h₂x
  have := h₂f x h₂x.1
  simp_all [← h₁x.analyticOrderAt_eq_zero, h₁x.meromorphicOrderAt_eq]

/-!
## Formula goes here
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {x c w : ℂ}

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
  have h₂f : (divisor f (sphere 0 R)).support.Finite :=
    (divisor f (sphere 0 R)).finiteSupport (isCompact_sphere 0 R)
  have h₃f : (divisor f (ball 0 R)).support.Finite := by
    apply ((divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
    intro b hb
    have h₂b := hb
    rw [mem_support, ne_eq, divisor_apply (fun c hc ↦ h₀f c (ball_subset_closedBall hc)) ((divisor f (ball 0 R)).supportWithinDomain hb)] at h₂b
    rwa [mem_support, ne_eq, divisor_apply h₀f (ball_subset_closedBall ((divisor f (ball 0 R)).supportWithinDomain hb))]
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
  -- Regularity properties of functions used in the calculatoin below
  have ρ₁ : ContinuousOn (fun x ↦ (re ∘ herglotzRieszKernel 0 w) (circleMap 0 R x)) (uIcc 0 (2 * π)) := by
    unfold herglotzRieszKernel
    apply Continuous.continuousOn
    have {x : ℝ} : circleMap 0 R x - w ≠ 0 := by
      by_contra h
      rw [← (sub_eq_zero.1 h), mem_ball, dist_zero_right, norm_circleMap_zero] at hw
      grind
    fun_prop (disch := aesop)
  have ρ₂ : CircleIntegrable (Complex.re ∘ herglotzRieszKernel 0 w • (Real.log ‖h ·‖)) 0 R := by
    apply IntervalIntegrable.continuousOn_mul _ ρ₁
    apply (AnalyticOnNhd.meromorphicOn _).intervalIntegrable_log_norm
    intro x hx
    apply AnalyticAt.comp' _ (analyticOnNhd_circleMap 0 R x (by tauto))
    apply AnalyticAt.restrictScalars (𝕜' := ℂ) (h₁h (circleMap 0 R x) _)
    simp [abs_of_nonneg hR.le]
  have ρ₃ : ∀ i ∈ h₂f.toFinset, CircleIntegrable ((divisor f (sphere 0 R)) i • re ∘ herglotzRieszKernel 0 w • (Real.log ‖· - i‖)) 0 R := by
    intro i hi
    rw [cast_smul]
    apply (IntervalIntegrable.continuousOn_mul _ ρ₁).const_mul
    apply (AnalyticOnNhd.meromorphicOn _).intervalIntegrable_log_norm
    exact AnalyticOnNhd.sub (fun x _ ↦ analyticOnNhd_circleMap 0 R x (mem_univ x)) (fun _ _ ↦ by fun_prop)
  -- Proof of the main claim by calculation
  calc circleAverage (re ∘ herglotzRieszKernel 0 w • (Real.log ‖f ·‖)) 0 R
    _ = circleAverage (re ∘ herglotzRieszKernel 0 w •
        (Real.log ‖(((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
          * (∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h) ·‖)) 0 R := by
      apply circleAverage_congr_codiscreteWithin _ hR.ne'
      rw [abs_of_pos hR]
      filter_upwards [h₁f.filter_mono (codiscreteWithin.mono sphere_subset_closedBall)]
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
      rw [cast_smul, circleAverage_smul, smul_eq_mul, smul_eq_mul]
      rw [circleAverage_re_herglotzRieszKernel_mul_log
        ((divisor f (sphere 0 R)).supportWithinDomain (h₂f.mem_toFinset.1 hx)) hw]
