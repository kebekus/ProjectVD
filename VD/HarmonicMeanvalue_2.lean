import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.HasPrimitives
import VD.MathlibPending.HarmonicContOnCl
import VD.MathlibSubmitted.Poisson

open Complex InnerProductSpace Metric Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℂ → E} {c : ℂ} {R : ℝ}

/--
The circle average of a continuous function is itself continuous, as a function
of the radius.
-/
theorem ContinuousOn.circleAverage {s : Set ℝ} {c : ℂ} (hs : ∀ r : s, 0 ≤ r.1)
    (hf : ContinuousOn f {z : ℂ | ‖z - c‖ ∈ s}) :
    ContinuousOn (circleAverage f c) s := by
  unfold Real.circleAverage
  rw [continuousOn_iff_continuous_restrict] at *
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  have η : ∀ x : s × ℝ, circleMap c x.1 x.2 ∈ {z | ‖z - c‖ ∈ s} :=
    fun x ↦ by simp [abs_of_nonneg (hs x.1)]
  apply hf.comp (f := (fun x ↦ ⟨circleMap c x.1 x.2, η x⟩))
  fun_prop [circleMap]


open InnerProductSpace Metric Real

variable {f : ℂ → ℝ} {c : ℂ} {R : ℝ}

/--
The **Mean Value Property** of harmonic functions: If `f : ℂ → ℝ` is harmonic in a neighborhood of a
closed disc of radius `R` and center `c`, then the circle average `circleAverage f c R` equals
`f c`.
-/
theorem HarmonicOnNhd.circleAverage_eq₀ (hf : HarmonicOnNhd f (closedBall c |R|)) :
    circleAverage f c R = f c := by
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c |R|).exists_thickening_subset_open
    (isOpen_setOf_harmonicAt f) hf
  rw [thickening_closedBall h₁e (abs_nonneg R)] at h₂e
  obtain ⟨F, h₁F, h₂F⟩ := harmonic_is_realOfHolomorphic h₂e
  have h₃F : DifferentiableOn ℂ F (closure (ball c |R|)) := by
    intro x hx
    apply (h₁F x _).differentiableWithinAt
    grind [mem_ball, mem_closedBall.1 (closure_ball_subset_closedBall hx)]
  have h₄F : Set.EqOn (Complex.reCLM ∘ F) f (sphere c |R|) :=
    fun x hx ↦ h₂F (sphere_subset_ball (lt_add_of_pos_left |R| h₁e) hx)
  rw [← circleAverage_congr_sphere h₄F, Complex.reCLM.circleAverage_comp_comm,
    h₃F.diffContOnCl.circleAverage]
  · apply h₂F
    simp [mem_ball, dist_self, add_pos_of_pos_of_nonneg h₁e (abs_nonneg R)]
  · apply (h₁F.continuousOn.mono (fun _ _ ↦ by simp_all [dist_eq_norm])).circleIntegrable'

theorem testCase₁ {f : ℝ → ℝ} {c R : ℝ} (hR : 0 < R)
    (η₀ : ContinuousOn f (Set.Icc 0 R))
    (η₁ : ∀ (r : (Set.Ico 0 R)), f ↑r = c) :
    f R = c := by
  -- By continuity of $f$ at $R$, we have $\lim_{r \to R^-} f(r) = f(R)$.
  have h_cont : Filter.Tendsto f (nhdsWithin R (Set.Iio R)) (nhds (f R)) := by
    have := η₀ R ( Set.right_mem_Icc.mpr hR.le );
    convert this.mono_left _ using 2
    rw [ nhdsWithin_le_iff ]
    exact mem_nhdsLT_iff_exists_Ioo_subset.mpr ⟨ 0, hR, fun x hx => ⟨ hx.1.le, hx.2.le ⟩ ⟩
  refine' tendsto_nhds_unique h_cont _
  exact tendsto_const_nhds.congr'
    ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhdsLT hR )
      fun x hx => by have := η₁ ⟨ x, ⟨ hx.1.le, hx.2 ⟩ ⟩ ; aesop )

theorem HarmonicOnNhd.circleAverage_eq₁₁ (h₁f : HarmonicOnNhd f (ball c |R|))
    (h₂f : ContinuousOn f (closedBall c |R|)) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp_all
  have η₀ : ContinuousOn (circleAverage f c) (Set.Icc 0 |R|) := by
    apply ContinuousOn.circleAverage
    · aesop
    · convert h₂f
      aesop
  have η₁ : ∀ r : Set.Ico 0 |R|, circleAverage f c r = f c := by
    intro r
    rw [HarmonicOnNhd.circleAverage_eq₀]
    apply h₁f.mono
    have : (0 : ℝ) ≤ r := by
      aesop
    rw [abs_of_nonneg this]
    have := r.2
    intro x hx
    simp_all
    apply hx.trans_lt
    aesop
  have η₃ : 0 < |R| := by
    aesop
  rw [← circleAverage_abs_radius]
  exact testCase₁ η₃ η₀ η₁
