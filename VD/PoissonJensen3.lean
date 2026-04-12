import VD.MathlibSubmitted.BlaschkeDecomp
import VD.BlaschkeDecomp2
import VD.MathlibSubmitted.Poisson_log_affine
import VD.MathlibSubmitted.Perfect
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.Complex.Harmonic.Poisson

open Complex Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution

/-!
## Additional Material
-/

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


lemma xx
    {f h : ℂ → E}
    (hw : w ∈ ball c R)
    (h₀f : MeromorphicOn f (closedBall 0 R)) -- can be deduced
    (h₁h : AnalyticOnNhd ℂ h (closedBall 0 R))
    (h₂h : ∀ u ∈ (closedBall 0 R), h u ≠ 0)
    (h₁f : f =ᶠ[codiscreteWithin (closedBall 0 R)]
      ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
        * (∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h) :
    circleAverage (re ∘ herglotzRieszKernel 0 w • (Real.log ‖f ·‖)) 0 R =
        ∑ᶠ (x : ℂ), (divisor f (sphere 0 R)) x • Real.log ‖w - x‖ + Real.log ‖h w‖ := by
  have hR : 0 < R := pos_of_mem_ball hw
  have η₀ : Set.Finite (divisor f (sphere 0 R)).support :=
    (divisor f (sphere 0 R)).finiteSupport (isCompact_sphere 0 R)
  calc circleAverage (re ∘ herglotzRieszKernel 0 w • (Real.log ‖f ·‖)) 0 R
    _ = circleAverage (re ∘ herglotzRieszKernel 0 w •
        (Real.log ‖(((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
          * (∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h) ·‖)) 0 R := by
      /-
      apply circleAverage_congr_codiscreteWithin
      · rw [abs_of_pos hR]
        have :  f =ᶠ[codiscreteWithin (sphere 0 R)]
            ((∏ᶠ (u : ℂ), canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) *
            ∏ᶠ (u : ℂ), (fun x ↦ x - u) ^ (divisor f (sphere 0 R)) u) • h := by
          apply h₁f.filter_mono
          apply codiscreteWithin.mono sphere_subset_closedBall
        filter_upwards [this] with a ha
        simp_all
      · exact hR.ne'
      -/
      sorry
    _ = circleAverage (re ∘ herglotzRieszKernel 0 w •
        (Real.log ‖(((∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h) ·‖)) 0 R := by
      /-
      apply circleAverage_congr_sphere
      rw [abs_of_pos hR]
      intro a ha
      simp only [zpow_neg, Pi.smul_apply', Pi.mul_apply, comp_apply]
      rw [norm_smul, norm_smul, norm_mul]
      congr
      convert one_mul (a := ‖(∏ᶠ (u : ℂ), (fun x ↦ x - u) ^ (divisor f (sphere 0 R)) u) a‖)
      have η₀ : Set.Finite (divisor f (ball 0 R)).support := by
        have ζ₁ : Set.Finite (divisor f (closedBall 0 R)).support :=
          (divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
        have ζ₂ : (divisor f (ball 0 R)).support ⊆ (divisor f (closedBall 0 R)).support := by
          intro b hb
          have h₂b := hb
          simp
          rw [divisor_apply]
          simp only [mem_support, ne_eq] at h₂b
          rw [divisor_apply] at h₂b
          exact h₂b
          · intro c hc
            apply h₀f c
            apply ball_subset_closedBall
            exact hc
          · exact (divisor f (ball 0 R)).supportWithinDomain hb
          · exact h₀f
          · apply ball_subset_closedBall
            exact (divisor f (ball 0 R)).supportWithinDomain hb
        apply Set.Finite.subset ζ₁ ζ₂
      rw [finprod_eq_prod_of_mulSupport_subset (s := η₀.toFinset)]
      simp
      apply Finset.prod_eq_one
      intro b hb
      rw [norm_canonicalFactor_eval_circle_eq_one _ ha]
      simp
      · exact (divisor f (ball 0 R)).supportWithinDomain ((Finite.mem_toFinset η₀).mp hb)
      · aesop
      -/
      sorry
    _ = circleAverage (re ∘ herglotzRieszKernel 0 w • fun x ↦
      Real.log ‖∏ u ∈ η₀.toFinset, (x - u) ^ (divisor f (sphere 0 R)) u‖ + Real.log ‖h x‖) 0 R:= by
      apply circleAverage_congr_codiscreteWithin
      rw [abs_of_pos (pos_of_mem_ball hw)]
      have : (divisor f (sphere 0 R)) =ᶠ[codiscreteWithin (sphere 0 R)] 0 := by
        exact (divisor f (sphere 0 R)).eq_zero_codiscreteWithin
      filter_upwards [(divisor f (sphere 0 R)).eq_zero_codiscreteWithin,
        Filter.self_mem_codiscreteWithin (sphere 0 R)] with a ha h₂a
      simp_all
      left
      rw [finprod_eq_prod_of_mulSupport_subset (s := η₀.toFinset)]
      rw [norm_smul]
      simp
      rw [Real.log_mul]
      · rw [Finset.prod_ne_zero_iff]
        intro b hb
        apply zpow_ne_zero
        simp
        by_contra hCon
        rw [sub_eq_zero] at hCon
        subst hCon
        simp at hb
        tauto
      · simp
        apply h₂h
        simp_all
      aesop
      exact hR.ne'
    _ = ∑ᶠ (x : ℂ), (divisor f (sphere 0 R)) x • Real.log ‖w - x‖ + Real.log ‖h w‖ := by
      sorry
  sorry
