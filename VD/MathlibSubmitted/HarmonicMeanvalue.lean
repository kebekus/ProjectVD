import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl

open InnerProductSpace Metric Real Set Topology
set_option backward.isDefEq.respectTransparency false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!
# Elsewhere
-/

/--
The circleMap for a fixed center is continuous as a function on `ℝ × ℝ`.
-/
@[fun_prop] lemma circleMap.continuous {c : ℂ} :
    Continuous (fun (x : ℝ × ℝ) ↦ circleMap c x.1 x.2) := by
  fun_prop [circleMap]

/--
The circle average of a continuous function is itself continuous, as a function
of the radius.
-/
theorem ContinuousOn.circleAverage {f : ℂ → E} {s : Set ℝ} {c : ℂ}
    (hf : ContinuousOn f {z : ℂ | ‖z - c‖ ∈ s})
    (hs : ∀ r : s, 0 ≤ r.1) :
    ContinuousOn (circleAverage f c) s := by
  unfold Real.circleAverage
  rw [continuousOn_iff_continuous_restrict] at *
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  have : ∀ x : s × ℝ, circleMap c x.1 x.2 ∈ {z | ‖z - c‖ ∈ s} :=
    fun x ↦ by simp [abs_of_nonneg (hs x.1)]
  apply hf.comp (f := (fun x ↦ ⟨circleMap c x.1 x.2, this x⟩))
  fun_prop

/--
Companion lemma to `ContinuousOn.circleAverage`: a function continuous on `Ioc r
R` and constant on `Ioo r R` is constant.
-/
lemma ContinuousOn.eq_of_eqOn_Ioo {f : ℝ → ℝ} {c r R : ℝ}
    (h₁f : ContinuousOn f (Ioc r R)) (hR : r < R)
    (h₂f : EqOn f (fun _ ↦ c) (Ioo r R)) :
    f R = c := by
  have : Filter.Tendsto f (𝓝[Iio R] R) (𝓝 (f R)) := by
    apply (h₁f R (right_mem_Ioc.mpr hR)).mono_left
    rw [nhdsWithin_le_iff, mem_nhdsLT_iff_exists_Ioo_subset]
    use r
    simp_all [Ioo_subset_Ioc_self]
  apply tendsto_nhds_unique this (tendsto_const_nhds.congr' _)
  apply Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hR) (fun _ hx ↦ (h₂f hx).symm)

/-!
# Mathlib.Analysis.Complex.Harmonic.MeanValue
-/

/--
The **Mean Value Property** of harmonic functions: If `f : ℂ → ℝ` is harmonic on
a disc of radius `|R|` and center `c` and continuous on its closure, then the
circle average `circleAverage f c R` equals `f c`.
-/
theorem HarmonicContOnCl.circleAverage_eq {f : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (h₁f : HarmonicContOnCl f (ball c |R|)) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp_all
  rw [← circleAverage_abs_radius]
  apply ((h₁f.2.mono _).circleAverage (·.2.1.le)).eq_of_eqOn_Ioo (by aesop)
  intro r hr
  apply HarmonicOnNhd.circleAverage_eq
  · apply h₁f.1.mono
    rw [abs_of_pos hr.1]
    exact closedBall_subset_ball hr.2
  · intro x hx
    rw [closure_ball _ (by aesop)]
    rw [mem_closedBall_iff_norm]
    exact hx.2
