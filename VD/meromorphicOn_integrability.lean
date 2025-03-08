import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Integral.CircleIntegral
import VD.specialFunctions_CircleIntegral_affine
import VD.stronglyMeromorphicOn_eliminate

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral


theorem MeromorphicOn.integrable_log_abs_f₀
  {f : ℂ → ℂ}
  {r : ℝ}
  -- WARNING: Not optimal. It suffices to be meromorphic on the Sphere
  (h₁f : MeromorphicOn f (Metric.closedBall (0 : ℂ) r))
  -- WARNING: Not optimal. This needs to go
  (hr : 0 < r)
   :
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

    have h₃f : Set.Finite (Function.support h₁f.divisor) := by
      exact h₁f.divisor.finiteSupport h₁U

    obtain ⟨g, h₁g, h₂g, h₃g⟩ := MeromorphicOn.decompose_log h₁U h₂U h₃U h₁f h₂f
    have : (fun z ↦ log ‖f (circleMap 0 r z)‖) = (fun z ↦ log ‖f z‖) ∘ (circleMap 0 r) := by
      rfl
    rw [this]
    have : Metric.sphere (0 : ℂ) |r| ⊆ Metric.closedBall (0 : ℂ) r := by
      rw [abs_of_pos hr]
      apply Metric.sphere_subset_closedBall

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
    have h {x : ℝ} : (Function.support fun s => (h₁f.divisor s) * log ‖circleMap 0 r x - s‖) ⊆ h₃f.toFinset := by
      intro x; simp; tauto
    simp_rw [finsum_eq_sum_of_support_subset _ h]
    have : (fun x => ∑ s ∈ h₃f.toFinset, (h₁f.divisor s) * log ‖circleMap 0 r x - s‖) = (∑ s ∈ h₃f.toFinset, fun x => (h₁f.divisor s) * log ‖circleMap 0 r x - s‖) := by
      ext x; simp
    rw [this]
    apply IntervalIntegrable.sum h₃f.toFinset
    intro s hs
    apply IntervalIntegrable.const_mul

    apply intervalIntegrable_logAbs_circleMap_sub_const hr.ne.symm

  · push_neg at h₂f

    let F := h₁f.makeStronglyMeromorphicOn
    have : (fun z => log ‖f z‖) =ᶠ[Filter.codiscreteWithin (Metric.closedBall 0 r)] (fun z => log ‖F z‖) := by
      -- WANT: apply Filter.eventuallyEq.congr
      let A := (makeStronglyMeromorphicOn_changeDiscrete'' h₁f)
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
      rw [← makeStronglyMeromorphicOn_changeOrder h₁f hx] at A
      let B := ((stronglyMeromorphicOn_of_makeStronglyMeromorphicOn h₁f) x hx).order_eq_zero_iff.not.1
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
