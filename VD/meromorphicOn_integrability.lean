import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Integral.CircleIntegral
import VD.specialFunctions_CircleIntegral_affine
import VD.Eliminate
import VD.stronglyMeromorphicOn_eliminate

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

theorem IntervalIntegrable.finsum {ι : Type u_1} {E : Type u_3} [NormedAddCommGroup E] {a b : ℝ}
    {μ : MeasureTheory.Measure ℝ} [IsLocallyFiniteMeasure μ] {f : ι → ℝ → E}
    (h : ∀ i, IntervalIntegrable (f i) μ a b) :
    IntervalIntegrable (∑ᶠ i, f i) μ a b := by
  by_cases h₁ : f.support.Finite
  · rw [finsum_eq_sum _ h₁]
    apply IntervalIntegrable.sum
    intro i hi
    exact h i
  · rw [finsum_of_infinite_support h₁]
    apply _root_.intervalIntegrable_const_iff.2
    tauto

theorem MeromorphicOn.intervalIntegrable_log_norm {f : ℝ → ℂ} {a b : ℝ}
    (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log ‖f ·‖) MeasureTheory.volume a b := by
  by_cases t₀ : ∀ u : [[a, b]], (hf u u.2).order ≠ ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles_log t₀
      ((divisor f [[a, b]]).finiteSupport isCompact_uIcc)
    rw [intervalIntegrable_congr_codiscreteWithin
      (h₃g.filter_mono (Filter.codiscreteWithin.mono Set.uIoc_subset_uIcc))]
    apply IntervalIntegrable.add
    · apply IntervalIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      rw [(by ring : a = ((a - i) + i)), (by ring : b = ((b - i) + i))]
      apply IntervalIntegrable.comp_sub_right (f := fun x ↦ log ‖x‖) _ i
      simp_rw [norm_eq_abs, log_abs]
      exact intervalIntegrable_log'
    · apply ContinuousOn.intervalIntegrable
      apply h₁g.continuousOn.norm.log
      simp_all
  · rw [← hf.exists_order_ne_top_iff_forall (isConnected_Icc inf_le_sup)] at t₀
    push_neg at t₀
    have : (fun x ↦ log ‖f x‖) =ᶠ[codiscreteWithin (Ι a b)] 0 := by
      apply Filter.EventuallyEq.filter_mono _ (Filter.codiscreteWithin.mono Set.uIoc_subset_uIcc)
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        Filter.codiscreteWithin_self [[a, b]]] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.order_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    rw [intervalIntegrable_congr_codiscreteWithin this]
    apply _root_.intervalIntegrable_const_iff.2
    tauto

theorem MeromorphicOn.intervalIntegrable_posLog_norm {f : ℝ → ℂ} {a b : ℝ}
    (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log⁺ ‖f ·‖) MeasureTheory.volume a b := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply IntervalIntegrable.add
  apply hf.intervalIntegrable_log_norm.const_mul
  apply (IntervalIntegrable.abs hf.intervalIntegrable_log_norm).const_mul

/-- Circle integrability is invariant when functions change along discrete sets. -/
theorem CircleIntegrable.congr_codiscreteWithin' {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℝ}
    (hf : f₁ =ᶠ[codiscreteWithin (Metric.sphere c |R|)] f₂) (hf₁ : CircleIntegrable f₁ c R) :
    CircleIntegrable f₂ c R := by
  by_cases hR : R = 0
  · simp [hR]
  apply (intervalIntegrable_congr_codiscreteWithin _).1 hf₁
  rw [eventuallyEq_iff_exists_mem]
  exact ⟨(circleMap c R)⁻¹' {z | f₁ z = f₂ z},
    codiscreteWithin.mono (by simp only [Set.subset_univ]) (circleMap_preimage_codiscrete hR hf),
    by tauto⟩

theorem CircleIntegrable.finsum {ι : Type u_1}
    {E : Type u_3} [NormedAddCommGroup E] {c : ℂ} {R : ℝ}
    {f : ι → ℂ → ℂ}
    (h : ∀ i, CircleIntegrable (f i) c R) :
    CircleIntegrable (∑ᶠ i, f i) c R := by
  unfold CircleIntegrable
  apply IntervalIntegrable.finsum
  sorry


theorem MeromorphicOn.circleIntegrable_log_norm {f : ℂ → ℂ} {r : ℝ}
    (hf : MeromorphicOn f (Metric.sphere 0 |r|)) :
    CircleIntegrable (log ‖f ·‖) 0 r := by
  by_cases t₀ : ∀ u : (Metric.sphere (0 : ℂ) |r|), (hf u u.2).order ≠ ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles_log t₀
      ((divisor f (Metric.sphere (0 : ℂ) |r|)).finiteSupport (isCompact_sphere 0 |r|))

    apply CircleIntegrable.congr_codiscreteWithin' h₃g.symm
    apply CircleIntegrable.add
    · unfold CircleIntegrable

      sorry
    · apply ContinuousOn.intervalIntegrable
      simp
      apply ContinuousOn.log
      apply ContinuousOn.norm
      apply ContinuousOn.comp (t := Metric.sphere 0 |r|)
      apply h₁g.continuousOn
      apply Continuous.continuousOn
      apply continuous_circleMap
      --
      intro x hx
      simp
      --
      intro x hx
      simp
      apply h₂g ⟨circleMap 0 r x, circleMap_mem_sphere' 0 r x⟩
  · sorry



theorem MeromorphicOn.integrable_log_abs_f₀ {f : ℂ → ℂ} {r : ℝ}
  -- WARNING: Not optimal. It suffices to be meromorphic on the Sphere
    (h₁f : MeromorphicOn f (Metric.closedBall (0 : ℂ) r))
  -- WARNING: Not optimal. This needs to go
    (hr : 0 < r) :
    IntervalIntegrable (fun z ↦ log ‖f (circleMap 0 r z)‖) MeasureTheory.volume 0 (2 * π) := by


  by_cases h₂f : ∃ u : (Metric.closedBall (0 : ℂ) r), (h₁f u u.2).order ≠ ⊤
  · have h₁U : IsCompact (Metric.closedBall (0 : ℂ) r) := isCompact_closedBall 0 r

    have h₂U : IsConnected (Metric.closedBall (0 : ℂ) r) := by
      constructor
      · exact Metric.nonempty_closedBall.mpr hr.le
      · exact (convex_closedBall (0 : ℂ) r).isPreconnected

    -- This is where we use 'ball' instead of sphere. However, better
    -- results should make this assumption unnecessary.
    have h₃U : interior (Metric.closedBall (0 : ℂ) r) ≠ ∅ := by
      rw [interior_closedBall, ← Set.nonempty_iff_ne_empty]
      use 0; simp [hr];
      repeat exact hr.ne.symm

    have h₃f : Set.Finite (Function.support (MeromorphicOn.divisor f (Metric.closedBall 0 r))) := by
      exact (MeromorphicOn.divisor f (Metric.closedBall 0 r)).finiteSupport h₁U

    have h₄f : ∀ u : (Metric.closedBall (0 : ℂ) r), (h₁f u u.2).order ≠ ⊤ := by
      sorry

    obtain ⟨g, h₁g, h₂g, h₃g⟩ := MeromorphicOn.extract_zeros_poles_log h₁f h₄f h₃f

    have : (fun z ↦ log ‖f (circleMap 0 r z)‖) = (fun z ↦ log ‖f z‖) ∘ (circleMap 0 r) := by
      rfl
    rw [this]
    have : Metric.sphere (0 : ℂ) |r| ⊆ Metric.closedBall (0 : ℂ) r := by
      rw [abs_of_pos hr]
      apply Metric.sphere_subset_closedBall
    simp_rw [add_comm] at h₃g
    rw [integrability_congr_changeDiscrete this (ne_of_lt hr).symm h₃g]

    apply IntervalIntegrable.add
    --
    apply Continuous.intervalIntegrable
    apply continuous_iff_continuousAt.2
    intro x
    have : (fun x => log ‖g (circleMap 0 r x)‖) = log ∘ norm ∘ g ∘ (fun x ↦ circleMap 0 r x) :=
      rfl
    rw [this]
    apply ContinuousAt.comp
    apply Real.continuousAt_log
    · simp
      have : (circleMap 0 r x) ∈ (Metric.closedBall (0 : ℂ) r) := by
        apply circleMap_mem_closedBall
        exact hr.le
      exact h₂g ⟨(circleMap 0 r x), this⟩
    apply ContinuousAt.comp
    · apply Continuous.continuousAt continuous_norm
    apply ContinuousAt.comp
    · have : (circleMap 0 r x) ∈ (Metric.closedBall (0 : ℂ) r) := by
        apply circleMap_mem_closedBall (0 : ℂ) hr.le x
      apply (h₁g (circleMap 0 r x) this).continuousAt
    apply Continuous.continuousAt (continuous_circleMap 0 r)
    --
    have h {x : ℝ} : (Function.support fun s => (MeromorphicOn.divisor f (Metric.closedBall 0 r) s) * log ‖circleMap 0 r x - s‖) ⊆ h₃f.toFinset := by
      intro x; simp; tauto
    simp_rw [finsum_eq_sum_of_support_subset _ h]
    have : (fun x => ∑ s ∈ h₃f.toFinset, (MeromorphicOn.divisor f (Metric.closedBall 0 r) s) * log ‖circleMap 0 r x - s‖) = (∑ s ∈ h₃f.toFinset, fun x => (MeromorphicOn.divisor f (Metric.closedBall 0 r) s) * log ‖circleMap 0 r x - s‖) := by
      ext x; simp
    rw [this]
    apply IntervalIntegrable.sum h₃f.toFinset
    intro s hs
    apply IntervalIntegrable.const_mul

    apply intervalIntegrable_logAbs_circleMap_sub_const hr.ne.symm

  · push_neg at h₂f

    let F := toMeromorphicNFOn f (Metric.closedBall 0 r)
    have : (fun z => log ‖f z‖) =ᶠ[Filter.codiscreteWithin (Metric.closedBall 0 r)] (fun z => log ‖F z‖) := by
      -- WANT: apply Filter.eventuallyEq.congr
      let A := (toMeromorphicNFOn_eqOn_codiscrete h₁f)
      obtain ⟨s, h₁s, h₂s⟩ := eventuallyEq_iff_exists_mem.1 A
      rw [eventuallyEq_iff_exists_mem]
      use s
      constructor
      · exact h₁s
      · intro x hx
        simp_rw [h₂s hx, F]
    have hU : Metric.sphere (0 : ℂ) |r| ⊆ Metric.closedBall 0 r := by
      rw [abs_of_pos hr]
      exact Metric.sphere_subset_closedBall
    have t₀ : (fun z => log ‖f (circleMap 0 r z)‖) =  (fun z => log ‖f z‖) ∘ circleMap 0 r := by
      rfl
    rw [t₀]
    clear t₀
    rw [integrability_congr_changeDiscrete hU (ne_of_lt hr).symm this]

    have : ∀ x ∈ Metric.closedBall 0 r, F x = 0 := by
      intro x hx
      let A := h₂f ⟨x, hx⟩
      rw [← order_toMeromorphicNFOn h₁f hx] at A
      let B := ((meromorphicNFOn_toMeromorphicNFOn f (Metric.closedBall 0 r)) hx).order_eq_zero_iff.not.1
      simp [A] at B
      assumption
    have : (fun z => log ‖F z‖) ∘ circleMap 0 r = 0 := by
      funext x
      simp
      left
      apply this
      simp [abs_of_pos hr]
    simp_rw [this]
    apply intervalIntegral.intervalIntegrable_const


theorem MeromorphicOn.integrable_log_abs_f
  {f : ℂ → ℂ}
  {r : ℝ}
  -- WARNING: Not optimal. It suffices to be meromorphic on the Sphere
  (h₁f : MeromorphicOn f (Metric.closedBall (0 : ℂ) |r|)) :
    IntervalIntegrable (fun z ↦ log ‖f (circleMap 0 r z)‖) MeasureTheory.volume 0 (2 * π) := by

  rcases lt_trichotomy r 0 with h|h|h
  · rw [abs_of_neg h] at h₁f
    simpa using integrability_congr_negRadius (f := fun z => log ‖f z‖) (r := -r) (h₁f.integrable_log_abs_f₀ (Left.neg_pos_iff.mpr h))
  · simp [h]
  · rw [abs_of_pos h] at h₁f
    exact h₁f.integrable_log_abs_f₀ h


theorem MeromorphicOn.integrable_poslog_abs_f
  {f : ℂ → ℂ}
  {r : ℝ}
  -- WARNING: Not optimal. It suffices to be meromorphic on the Sphere
  (h₁f : MeromorphicOn f (Metric.closedBall (0 : ℂ) |r|)) :
  IntervalIntegrable (fun z ↦ posLog ‖f (circleMap 0 r z)‖) MeasureTheory.volume 0 (2 * π) := by

  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply IntervalIntegrable.add
  apply h₁f.integrable_log_abs_f.const_mul
  apply (IntervalIntegrable.abs h₁f.integrable_log_abs_f).const_mul
