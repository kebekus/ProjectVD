import VD.MathlibPending.BlaschkeDecomp
import VD.MathlibSubmitted.Poisson_log_affine

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution


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

theorem PoissonJensen {w ρ c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤)
    (hρ : ρ ∈ sphere c R) (hw : w ∈ ball c R) :
    circleAverage ((Complex.re ∘ herglotzRieszKernel c w) • (log ‖f ·‖)) 0 R = 0 := by
  have h₃f : MeromorphicOn f (sphere 0 R) := h₁f.mono_set sphere_subset_closedBall
  have h₄f : ∀ u ∈ (sphere (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤ := by
    intro u hu
    apply h₂f ⟨u, sphere_subset_closedBall hu⟩
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := canonicalDecomposition h₁f h₂f
  have h₅g : MeromorphicOn g (sphere 0 R) := h₁g.meromorphicOn.mono_set sphere_subset_closedBall
  have h₆g : ∀ u ∈ (sphere (0 : ℂ) R), meromorphicOrderAt g u ≠ ⊤ := by
    intro u hu
    apply h₁g.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_closedBall
      (mem_closedBall_self (pos_of_mem_ball hw).le) (sphere_subset_closedBall hu)
    simp [(h₁g (mem_closedBall_self (pos_of_mem_ball hw).le)).meromorphicOrderAt_eq_zero_iff.2
      (h₂g 0 (mem_ball_self (pos_of_mem_ball hw)))]
  have η₀ : Set.Finite (fun u ↦ Complex.canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)).mulSupport := by
    sorry
  rw [finprod_eq_prod _ η₀] at h₃g
  have η₁ : (log ‖f ·‖) =ᶠ[codiscreteWithin (sphere 0 R)] (log ‖g ·‖) := by
    have h₄g : f =ᶠ[codiscreteWithin (sphere 0 R)]
        (∏ i ∈ η₀.toFinset, Complex.canonicalFactor R i ^ (-(divisor f (ball 0 R)) i)) • g := by
      apply h₃g.filter_mono (Filter.codiscreteWithin.mono sphere_subset_closedBall)
    filter_upwards [h₄g, Filter.self_mem_codiscreteWithin _,
      h₅g.codiscreteWithin_setOf_ne_zero h₆g] with x h₁x h₂x h₃x
    rw [h₁x]
    simp
    rw [log_mul]
    rw [Finset.prod_eq_one]
    simp
    --
    · intro i hi
      have : i ∈ ball 0 R := by
        -- aesop alone can do that, but is slow
        by_contra h
        have := (divisor f (ball 0 R)).apply_eq_zero_of_notMem h
        aesop
      simp [Complex.norm_canonicalFactor_eval_circle_eq_one this h₂x]
    · rw [ne_eq, inv_eq_zero, ← ne_eq]
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      have : i ∈ ball 0 R := by
        -- aesop alone can do that, but is slow
        by_contra h
        have := (divisor f (ball 0 R)).apply_eq_zero_of_notMem h
        aesop
      simp [Complex.norm_canonicalFactor_eval_circle_eq_one this h₂x]
    · simp_all
  calc circleAverage (Complex.re ∘ herglotzRieszKernel c w • fun x ↦ log ‖f x‖) 0 R
    _ = circleAverage (Complex.re ∘ herglotzRieszKernel c w • fun x ↦ log ‖g x‖) 0 R := by
      apply circleAverage_congr_codiscreteWithin
      simp_rw [abs_of_pos (pos_of_mem_ball hw)]
      have h₄g : f =ᶠ[codiscreteWithin (sphere 0 R)]
        (∏ i ∈ η₀.toFinset, Complex.canonicalFactor R i ^ (-(divisor f (ball 0 R)) i)) • g := by
        apply h₃g.filter_mono (Filter.codiscreteWithin.mono sphere_subset_closedBall)
      filter_upwards [h₄g, Filter.self_mem_codiscreteWithin _,
        h₅g.codiscreteWithin_setOf_ne_zero h₆g] with x h₁x h₂x h₃x
      simp
      left
      rw [h₁x]
      simp
      rw [log_mul]
      rw [Finset.prod_eq_one]
      simp
      --
      · intro i hi
        have : i ∈ ball 0 R := by
          -- aesop alone can do that, but is slow
          by_contra h
          have := (divisor f (ball 0 R)).apply_eq_zero_of_notMem h
          aesop
        simp [Complex.norm_canonicalFactor_eval_circle_eq_one this h₂x]
      · rw [ne_eq, inv_eq_zero, ← ne_eq]
        rw [Finset.prod_ne_zero_iff]
        intro i hi
        have : i ∈ ball 0 R := by
          -- aesop alone can do that, but is slow
          by_contra h
          have := (divisor f (ball 0 R)).apply_eq_zero_of_notMem h
          aesop
        simp [Complex.norm_canonicalFactor_eval_circle_eq_one this h₂x]
      · simp_all
      · exact (pos_of_mem_ball hw).ne.symm
    _ = 0 := by

      sorry
