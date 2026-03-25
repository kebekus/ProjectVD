import VD.MathlibPending.BlaschkeDecomp
import VD.MathlibSubmitted.Poisson_log_affine

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution


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

theorem PoissonJensen_aux₀ {w c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤)
    (hw : w ∈ ball c R) :
    ∃ g : ℂ → ℂ,
      MeromorphicNFOn g (closedBall 0 R)
      ∧ (∀ u ∈ ball (0 : ℂ) R, g u ≠ 0)
      ∧ f =ᶠ[codiscreteWithin (closedBall 0 R)]
        (∏ᶠ (u : ℂ), Complex.canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) • g
      ∧ circleAverage ((Complex.re ∘ herglotzRieszKernel c w) • (log ‖f ·‖)) 0 R
        = circleAverage ((Complex.re ∘ herglotzRieszKernel c w) • (log ‖g ·‖)) 0 R := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := canonicalDecomposition h₁f h₂f
  use g, h₁g, h₂g, h₃g
  have h₅g : MeromorphicOn g (sphere 0 R) := h₁g.meromorphicOn.mono_set sphere_subset_closedBall
  have h₆g : ∀ u ∈ (sphere (0 : ℂ) R), meromorphicOrderAt g u ≠ ⊤ := by
    intro u hu
    apply h₁g.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_closedBall
      (mem_closedBall_self (pos_of_mem_ball hw).le) (sphere_subset_closedBall hu)
    simp [(h₁g (mem_closedBall_self (pos_of_mem_ball hw).le)).meromorphicOrderAt_eq_zero_iff.2
      (h₂g 0 (mem_ball_self (pos_of_mem_ball hw)))]
  apply circleAverage_congr_codiscreteWithin _ (pos_of_mem_ball hw).ne'
  simp_rw [abs_of_pos (pos_of_mem_ball hw)]
  filter_upwards [h₃g.filter_mono (Filter.codiscreteWithin.mono sphere_subset_closedBall),
    Filter.self_mem_codiscreteWithin _,
    h₅g.codiscreteWithin_setOf_ne_zero h₆g] with x h₁x h₂x h₃x
  simp
  left
  rw [h₁x]
  simp
  have : ‖(∏ᶠ (u : ℂ), (Complex.canonicalFactor R u ^ (divisor f (ball 0 R)) u)⁻¹) x‖ = 1 := by
    by_cases hf : Set.Finite
      (fun u ↦ (Complex.canonicalFactor R u ^ (divisor f (ball 0 R)) u)⁻¹).mulSupport
    · rw [finprod_eq_prod _ hf, Finset.prod_apply, norm_prod, Finset.prod_eq_one]
      intro a ha
      by_cases ha : a ∈ ball 0 R
      · simp [Complex.norm_canonicalFactor_eval_circle_eq_one ha h₂x]
      · simp_all
    · rw [finprod_of_infinite_mulSupport (Set.not_finite.mp hf)]
      simp
  rw [log_mul (by simp_all) (by simp_all)]
  simp_all

theorem PoissonJensen_aux₁ {w c : ℂ} {R : ℝ} {f g : ℂ → ℂ}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤)
    (hw : w ∈ ball c R)
    (h₁g : MeromorphicNFOn g (closedBall (0 : ℂ) R))
    (h₂g : ∀ u ∈ ball (0 : ℂ) R, g u ≠ 0)
    (h₃g : f =ᶠ[codiscreteWithin (closedBall 0 R)]
        (∏ᶠ (u : ℂ), Complex.canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) • g)
    (h₄g : circleAverage ((Complex.re ∘ herglotzRieszKernel c w) • (log ‖f ·‖)) 0 R
        = circleAverage ((Complex.re ∘ herglotzRieszKernel c w) • (log ‖g ·‖)) 0 R) :
    ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (closedBall 0 R)
      ∧ (∀ u ∈ closedBall (0 : ℂ) R, h u ≠ 0)
      ∧ g =ᶠ[codiscreteWithin (closedBall 0 R)]
          (∏ᶠ (u : ℂ), (fun x ↦ x - u) ^ (divisor g (closedBall 0 R)) u) • h
      ∧ circleAverage ((Complex.re ∘ herglotzRieszKernel c w) • (log ‖g ·‖)) 0 R
        = circleAverage ((Complex.re ∘ herglotzRieszKernel c w)
          • (fun x ↦ ∑ᶠ (i : ℂ), ↑((divisor g (closedBall 0 R)) i) * log ‖x - i‖ + log ‖h x‖)) 0 R := by
  have h₅g : ∀ (u : ↑(closedBall (0 : ℂ) R)), meromorphicOrderAt g ↑u ≠ ⊤ := by

    sorry
  have h₆g : (divisor g (closedBall 0 R)).support.Finite :=
    (divisor g (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
  obtain ⟨h, h₁h, h₂h, h₃h⟩ := h₁g.meromorphicOn.extract_zeros_poles h₅g h₆g
  use h, h₁h, (h₂h ⟨·, ·⟩), h₃h
  apply circleAverage_congr_codiscreteWithin _ (pos_of_mem_ball hw).ne'
  simp_rw [abs_of_pos (pos_of_mem_ball hw)]
  have : (divisor g (closedBall 0 R)).supportᶜ ∈ codiscreteWithin (sphere 0 R) := by
    apply Filter.codiscreteWithin.mono (subset_univ _) (codiscrete_le_cofinite _)
    simp [h₆g]
  filter_upwards [h₃h.filter_mono (Filter.codiscreteWithin.mono sphere_subset_closedBall),
    Filter.self_mem_codiscreteWithin _, this] with x h₁x h₂x h₃x
  simp
  left
  rw [h₁x]
  simp
  rw [log_mul]
  rw [finprod_eq_prod_of_mulSupport_subset (s := h₆g.toFinset)]
  rw [Finset.prod_apply]
  simp_rw [Pi.pow_apply]
  rw [norm_prod]
  simp_rw [norm_zpow]
  rw [log_prod]
  simp_rw [log_zpow]
  rw [← finsum_eq_sum_of_support_subset (s := h₆g.toFinset)]
  · intro a ha
    aesop
  · intro a ha
    simp at ha
    apply zpow_ne_zero
    simp
    by_contra h
    rw [sub_eq_zero] at h
    subst h
    aesop
  · intro a ha
    aesop
  · rw [ne_eq, norm_eq_zero, ← ne_eq]
    by_cases h : Set.Finite (fun u ↦ (fun x ↦ x - u) ^ (divisor g (closedBall 0 R)) u).mulSupport
    · rw [finprod_eq_prod _ h, Finset.prod_apply]
      rw [Finset.prod_ne_zero_iff]
      intro a ha
      simp_all
      apply zpow_ne_zero
      simp
      by_contra h
      rw [sub_eq_zero] at h
      subst h
      aesop
    · simp [finprod_of_infinite_mulSupport h]
  · simp [h₂h ⟨x, sphere_subset_closedBall h₂x⟩]

theorem PoissonJensen {w ρ c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤)
    (hρ : ρ ∈ sphere c R) (hw : w ∈ ball c R) :
    ∃ g : ℂ → ℂ,
      MeromorphicNFOn g (closedBall 0 R)
      ∧ (∀ u ∈ ball (0 : ℂ) R, g u ≠ 0)
      ∧ f =ᶠ[codiscreteWithin (closedBall 0 R)]
        (∏ᶠ (u : ℂ), Complex.canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) • g
      ∧ circleAverage ((Complex.re ∘ herglotzRieszKernel c w) • (log ‖f ·‖)) 0 R
        = circleAverage ((Complex.re ∘ herglotzRieszKernel c w) • (log ‖g ·‖)) 0 R := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := canonicalDecomposition h₁f h₂f
  use g, h₁g, h₂g, h₃g
  have h₅g : MeromorphicOn g (sphere 0 R) := h₁g.meromorphicOn.mono_set sphere_subset_closedBall
  have h₆g : ∀ u ∈ (sphere (0 : ℂ) R), meromorphicOrderAt g u ≠ ⊤ := by
    intro u hu
    apply h₁g.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_closedBall
      (mem_closedBall_self (pos_of_mem_ball hw).le) (sphere_subset_closedBall hu)
    simp [(h₁g (mem_closedBall_self (pos_of_mem_ball hw).le)).meromorphicOrderAt_eq_zero_iff.2
      (h₂g 0 (mem_ball_self (pos_of_mem_ball hw)))]
  have h₇g : ∀ (u : (closedBall (0 : ℂ) R)), meromorphicOrderAt g ↑u ≠ ⊤ := by
    sorry
  have h₈g : (divisor g (closedBall 0 R)).support.Finite := by
    sorry
  obtain ⟨h, h₁h, h₂h, h₃h⟩ := h₁g.meromorphicOn.extract_zeros_poles h₇g h₈g

  calc circleAverage (Complex.re ∘ herglotzRieszKernel c w • fun x ↦ log ‖f x‖) 0 R
    _ = circleAverage (Complex.re ∘ herglotzRieszKernel c w • fun x ↦ log ‖g x‖) 0 R := by
      apply circleAverage_congr_codiscreteWithin _ (pos_of_mem_ball hw).ne'
      simp_rw [abs_of_pos (pos_of_mem_ball hw)]
      filter_upwards [h₃g.filter_mono (Filter.codiscreteWithin.mono sphere_subset_closedBall),
        Filter.self_mem_codiscreteWithin _,
        h₅g.codiscreteWithin_setOf_ne_zero h₆g] with x h₁x h₂x h₃x
      simp
      left
      rw [h₁x]
      simp
      have : ‖(∏ᶠ (u : ℂ), (Complex.canonicalFactor R u ^ (divisor f (ball 0 R)) u)⁻¹) x‖ = 1 := by
        by_cases hf : Set.Finite
          (fun u ↦ (Complex.canonicalFactor R u ^ (divisor f (ball 0 R)) u)⁻¹).mulSupport
        · rw [finprod_eq_prod _ hf, Finset.prod_apply, norm_prod, Finset.prod_eq_one]
          intro a ha
          by_cases ha : a ∈ ball 0 R
          · simp [Complex.norm_canonicalFactor_eval_circle_eq_one ha h₂x]
          · simp_all
        · rw [finprod_of_infinite_mulSupport (Set.not_finite.mp hf)]
          simp
      rw [log_mul (by simp_all) (by simp_all)]
      simp_all
    _ = circleAverage (Complex.re ∘ herglotzRieszKernel c w
        • fun x ↦ log ‖((∏ᶠ (u : ℂ), (fun x ↦ x - u) ^ (divisor g (closedBall 0 R)) u) • h) x‖) 0 R := by
      apply circleAverage_congr_codiscreteWithin _ (pos_of_mem_ball hw).ne'
      simp_rw [abs_of_pos (pos_of_mem_ball hw)]
      filter_upwards [h₃h.filter_mono (Filter.codiscreteWithin.mono sphere_subset_closedBall),
        Filter.self_mem_codiscreteWithin _,
        h₅g.codiscreteWithin_setOf_ne_zero h₆g] with x h₁x h₂x h₃x
      simp
      left
      rw [h₁x]
      simp
    _ = circleAverage (Complex.re ∘ herglotzRieszKernel c w
        • (fun x ↦ log ‖(∏ᶠ (u : ℂ), (x - u) ^ (divisor g (closedBall 0 R)) u)‖ + log ‖h x‖)) 0 R := by
      apply circleAverage_congr_codiscreteWithin _ (pos_of_mem_ball hw).ne'
      congr
      sorry
    _ = 0 := by
      simp
      sorry
