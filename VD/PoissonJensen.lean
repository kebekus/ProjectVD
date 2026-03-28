import VD.MathlibPending.BlaschkeDecomp
import VD.MathlibSubmitted.Poisson_log_affine
import Mathlib.LinearAlgebra.Complex.Module

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
  have : ‖(∏ᶠ (u : ℂ), (Complex.canonicalFactor R u ^ (divisor f (ball 0 R)) u)⁻¹) x‖ = 1 := by
    by_cases hf : Set.Finite
        (fun u ↦ (Complex.canonicalFactor R u ^ (divisor f (ball 0 R)) u)⁻¹).mulSupport
    · rw [finprod_eq_prod _ hf, Finset.prod_apply, norm_prod, Finset.prod_eq_one]
      intro a _
      by_cases ha : a ∈ ball 0 R
      · simp [Complex.norm_canonicalFactor_eval_circle_eq_one ha h₂x]
      · simp_all
    · simp [finprod_of_infinite_mulSupport (Set.not_finite.mp hf)]
  simp_all

theorem PoissonJensen_aux₁ {w c : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hw : w ∈ ball c R)
    (h₁g : MeromorphicNFOn g (closedBall (0 : ℂ) R))
    (h₂g : ∀ u ∈ ball (0 : ℂ) R, g u ≠ 0) :
    ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (closedBall 0 R)
      ∧ (∀ u ∈ closedBall (0 : ℂ) R, h u ≠ 0)
      ∧ g =ᶠ[codiscreteWithin (closedBall 0 R)]
          (∏ᶠ (u : ℂ), (fun x ↦ x - u) ^ (divisor g (closedBall 0 R)) u) • h
      ∧ circleAverage ((Complex.re ∘ herglotzRieszKernel c w) • (log ‖g ·‖)) 0 R
        = circleAverage ((Complex.re ∘ herglotzRieszKernel c w)
          • (∑ᶠ (i : ℂ), (fun x ↦ ↑((divisor g (closedBall 0 R)) i) * log ‖x - i‖) + ((fun x ↦ log ‖h x‖)))) 0 R := by
  have h₅g : ∀ (u : ↑(closedBall (0 : ℂ) R)), meromorphicOrderAt g ↑u ≠ ⊤ := by
    rw [← MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall]
    have s₀ : (0 : ℂ) ∈ ball 0 R := by
      simp [pos_of_mem_ball hw]
    have : (0 : ℂ) ∈ closedBall 0 R := by
      simp [(pos_of_mem_ball hw).le]
    use ⟨0, this⟩
    simp only []
    rw [(h₁g this).meromorphicOrderAt_eq_zero_iff.2 (h₂g 0 s₀)]
    simp
    exact h₁g.meromorphicOn
    refine isConnected_closedBall (pos_of_mem_ball hw).le
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
  simp only [Pi.smul_apply', comp_apply, smul_eq_mul, mul_eq_mul_left_iff]
  left
  rw [h₁x, Pi.smul_apply', smul_eq_mul, Complex.norm_mul, log_mul]
  rw [finprod_eq_prod_of_mulSupport_subset (s := h₆g.toFinset)]
  rw [finsum_eq_sum_of_support_subset (s := h₆g.toFinset)]
  rw [Finset.prod_apply]
  simp_rw [Pi.pow_apply]
  rw [norm_prod]
  simp_rw [norm_zpow]
  rw [log_prod]
  simp_rw [log_zpow]
  simp
  · intro a ha
    simp at ha
    rw [zpow_ne_zero_iff]
    simp
    by_contra h
    rw [sub_eq_zero] at h
    subst h
    simp_all
    tauto
  · intro a ha
    simp_all
    by_contra h
    simp [h] at ha
    exact false_of_ne ha
  · intro a ha
    simp
    simp at ha
    aesop
  · rw [ne_eq, norm_eq_zero, ← ne_eq]
    by_cases h : Set.Finite (fun u ↦ (fun x ↦ x - u) ^ (divisor g (closedBall 0 R)) u).mulSupport
    · rw [finprod_eq_prod _ h, Finset.prod_apply]
      rw [Finset.prod_ne_zero_iff]
      intro a ha
      apply zpow_ne_zero
      simp only [ne_eq]
      by_contra h
      rw [sub_eq_zero] at h
      aesop
    · simp [finprod_of_infinite_mulSupport h]
  · simp [h₂h ⟨x, sphere_subset_closedBall h₂x⟩]

set_option backward.isDefEq.respectTransparency false in
theorem PoissonJensen_aux₂ {w : ℂ} {R : ℝ} {g h : ℂ → ℂ}
    (hw : w ∈ ball 0 R)
    (h₁g : MeromorphicNFOn g (closedBall (0 : ℂ) R))
    (h₂g : ∀ u ∈ ball (0 : ℂ) R, g u ≠ 0)
    (h₁h : AnalyticOnNhd ℂ h (closedBall 0 R)) :
    circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w)
        • (∑ᶠ (i : ℂ), (fun x ↦ ((divisor g (closedBall 0 R)) i) * log ‖x - i‖) + ((fun x ↦ log ‖h x‖)))) 0 R
      = ∑ᶠ x, ↑((divisor g (closedBall 0 R)) x) • log ‖w - x‖
        + circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • (fun x ↦ log ‖h x‖)) 0 R := by
  have μ₁ : (divisor g (closedBall 0 R)).support ⊆ sphere 0 R := by
    intro a
    contrapose
    simp_all only [ne_eq, mem_support, Decidable.not_not]
    intro ha
    rcases lt_trichotomy ‖a‖ R with h|h|h
    · have h₁a : a ∈ closedBall 0 R := by simpa [mem_closedBall_iff_norm] using h.le
      have h₂a := (h₁g  h₁a).meromorphicOrderAt_eq_zero_iff
      have h₃a := h₂g a (by aesop)
      have := h₂a.2 h₃a
      rw [h₁g.meromorphicOn.divisor_apply h₁a]
      aesop
    · aesop
    · aesop
  have η₂ : ContinuousOn (fun x ↦ (Complex.re ∘ herglotzRieszKernel 0 w) (circleMap 0 R x)) (uIcc 0 (2 * π)) := by
    unfold herglotzRieszKernel
    apply Continuous.continuousOn
    have : ∀ (x : ℝ), circleMap 0 R x - w ≠ 0 := by
      intro x
      by_contra h
      simp [← (sub_eq_zero.1 h)] at hw
      grind
    fun_prop (disch := aesop)
  have η₀ : CircleIntegrable (Complex.re ∘ herglotzRieszKernel 0 w • fun x ↦ log ‖h x‖) 0 R := by
    apply IntervalIntegrable.continuousOn_mul
    · -- IntervalIntegrable (fun x ↦ (fun x ↦ log ‖h x‖) (circleMap 0 R x)) MeasureTheory.volume 0 (2 * π)
      apply intervalIntegrable_log_norm_meromorphicOn
      apply AnalyticOnNhd.meromorphicOn
      intro x hx
      apply AnalyticAt.comp'
      have : AnalyticAt ℂ h (circleMap 0 R x) := by
        apply h₁h (circleMap 0 R x)
        simp
        rw [abs_of_nonneg]
        exact (pos_of_mem_ball hw).le
      exact AnalyticAt.restrictScalars this
      exact analyticOnNhd_circleMap 0 R x (by tauto)
    · exact η₂
  have h₁F : Set.Finite (divisor g (closedBall 0 R)).support :=
    (divisor g (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
  have η₁ : ∀ i ∈ h₁F.toFinset, CircleIntegrable
    (Complex.re ∘ herglotzRieszKernel 0 w * fun x ↦ ↑((divisor g (closedBall 0 R)) i) * log ‖x - i‖) 0 R := by
    intro i hi
    unfold CircleIntegrable
    apply IntervalIntegrable.continuousOn_mul
    · apply IntervalIntegrable.const_mul
      apply intervalIntegrable_log_norm_meromorphicOn
      apply AnalyticOnNhd.meromorphicOn
      apply AnalyticOnNhd.sub
      · intro x hx
        exact analyticOnNhd_circleMap 0 R x (by tauto)
      · intro x hx
        fun_prop
    · exact η₂
  rw [smul_add]
  rw [circleAverage_add]
  simp
  rw [finsum_eq_sum_of_support_subset (s := h₁F.toFinset)]
  rw [finsum_eq_sum_of_support_subset (s := h₁F.toFinset)]
  rw [Finset.mul_sum]
  rw [circleAverage_sum]
  have {i : ℂ} : Complex.re ∘ herglotzRieszKernel 0 w * (fun x ↦ ((divisor g (closedBall 0 R)) i) * log ‖x - i‖)
      = (((divisor g (closedBall 0 R)) i) : ℝ) • (Complex.re ∘ herglotzRieszKernel 0 w * (fun x ↦ log ‖x - i‖)) := by
    ext a
    simp
    ring
  simp_rw [this]
  clear this
  simp_rw [circleAverage_smul]
  apply Finset.sum_congr
  rfl
  intro a ha
  simp
  left
  have h₁a : a ∈ sphere (0 : ℂ) R := by
    aesop
  apply circleAverage_re_herglotzRieszKernel_mul_log h₁a hw
  · -- ∀ i ∈ h₁F.toFinset, CircleIntegrable (Complex.re ∘ herglotzRieszKernel 0 w * fun x ↦ ↑(F i) * log ‖x - i‖) 0 R
    exact η₁
  · intro x hx
    aesop
  · intro x
    contrapose
    aesop
  · by_cases h : Set.Finite (fun i ↦ (fun x ↦ ↑((divisor g (closedBall 0 R)) i) * log ‖x - i‖)).support
    · rw [finsum_eq_sum _ h]
      rw [Finset.smul_sum]
      apply CircleIntegrable.sum
      -- We have that above
      -- ∀ i ∈ h₁F.toFinset, CircleIntegrable (Complex.re ∘ herglotzRieszKernel 0 w * fun x ↦ ↑(F i) * log ‖x - i‖) 0 R
      intro i hi
      apply η₁
      simp
      simp at hi
      by_contra h
      simp_all
      tauto
    · simp [finsum_of_infinite_support h, CircleIntegrable]
  · -- CircleIntegrable (Complex.re ∘ herglotzRieszKernel 0 w • fun x ↦ log ‖h x‖) 0 R
    exact η₀

theorem PoissonJensen_aux₃ {w c : ℂ} {R : ℝ} {f g : ℂ → ℂ}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤)
    (hw : w ∈ ball (0 : ℂ) R) :
    ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (closedBall 0 R)
      ∧ (∀ u ∈ closedBall (0 : ℂ) R, h u ≠ 0)
      ∧ f =ᶠ[codiscreteWithin (closedBall 0 R)]
        (∏ᶠ (u : ℂ), (Complex.canonicalFactor R u ^ (divisor f (ball 0 R)) u)⁻¹)
          * ((∏ᶠ (u : ℂ), (fun x ↦ x - u) ^ (divisor f (sphere 0 R)) u) * h)
      ∧ circleAverage (Complex.re ∘ herglotzRieszKernel 0 w • fun x ↦ log ‖f x‖) 0 R =
        ∑ᶠ (x : ℂ), (divisor f (sphere 0 R)) x • log ‖w - x‖
        + circleAverage (Complex.re ∘ herglotzRieszKernel 0 w • fun x ↦ log ‖h x‖) 0 R := by
  obtain ⟨g, h₁g, h₂g, h₃g, h₄g⟩ := PoissonJensen_aux₀ h₁f h₂f hw
  have h₅g {u : ℂ}: (divisor g (closedBall 0 R)) u = (divisor f (sphere 0 R)) u := by
    sorry
  have h₆g : (∏ᶠ (u : ℂ), (fun x ↦ x - u) ^ (divisor g (closedBall 0 R)) u)
      = (∏ᶠ (u : ℂ), (fun x ↦ x - u) ^ (divisor f (sphere 0 R)) u) := by
    simp_rw [h₅g]
  obtain ⟨h, h₁h, h₂h, h₃h, h₄h⟩ := PoissonJensen_aux₁ hw h₁g h₂g
  rw [← h₄g] at h₄h
  rw [PoissonJensen_aux₂ hw h₁g h₂g h₁h] at h₄h
  simp_rw [h₅g] at h₄h
  use h
  simp_all
  filter_upwards [h₃g, h₃h] with a h₁a h₂a
  rw [h₁a]
  rw [Pi.mul_apply]
  rw [h₂a]
  simp
