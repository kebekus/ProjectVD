/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Integral.CircleAverage
import VD.Manifold.SectionDivisor

/-!
# The Proximity Function of a Section of a Line Bundle Along a Curve

Let `L` be a line bundle with continuous fibre norm over a manifold `B`, `σ` a section of `L`, and
`f : ℂ → B` a holomorphic map. The *proximity function* `ValueDistribution.proximitySection f σ` of
value distribution theory is the circle average of `log (1 / ‖σ (f ·)‖)`; it measures how close
`f` comes to the zero locus of `σ` on the circle of radius `r`. This follows the conventions of
[Noguchi–Winkelmann, *Nevanlinna theory in several complex variables and Diophantine
approximation*][MR3156076], Section 2.7: the proximity function is defined with `log`, not with
`log⁺`, and the normalization `1/(2π)` is part of `circleAverage`.

## Main results

- `Bundle.AnalyticAlong.circleIntegrable_log_norm`: `log ‖σ (f ·)‖` is circle integrable. The
  function is locally of the form `log ‖analytic‖ + continuous`, and the general patching lemma
  `circleIntegrable_of_forall_exists_intervalIntegrable` assembles local interval integrability
  into circle integrability.
- `ValueDistribution.proximitySection_sub_proximitySection`: the difference of the proximity
  functions of two sections `σ`, `τ` of the same line bundle is the circle average of
  `log ‖(σ/τ) ∘ f‖`. Together with Jensen's formula, this is the First Main Theorem.
- `ValueDistribution.neg_posLog_le_proximitySection`: if `‖σ‖ ≤ C`, then `-log⁺ C ≤ m(r)`. In
  particular, the proximity function is bounded from below when the base is compact.
-/

open Bundle Filter MeasureTheory Metric Real Set Topology
open scoped Interval

/-!
## Circle integrability of locally interval integrable functions
-/

/-- A function on the complex plane is circle integrable as soon as its restriction to the circle
is interval integrable near every point of the parametrization. -/
theorem circleIntegrable_of_forall_exists_intervalIntegrable {E : Type*} [NormedAddCommGroup E]
    {u : ℂ → E} {c : ℂ} {R : ℝ}
    (h : ∀ θ : ℝ, ∃ δ > 0,
      IntervalIntegrable (fun θ ↦ u (circleMap c R θ)) volume (θ - δ) (θ + δ)) :
    CircleIntegrable u c R := by
  unfold CircleIntegrable
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)]
  refine LocallyIntegrableOn.integrableOn_isCompact (fun θ _ ↦ ?_) isCompact_Icc
  obtain ⟨δ, hδ, h⟩ := h θ
  exact ⟨Icc (θ - δ) (θ + δ), mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)),
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 h⟩

variable {B : Type*} [TopologicalSpace B]
  {L : B → Type*} [TopologicalSpace (TotalSpace ℂ L)] [∀ x, NormedAddCommGroup (L x)]
  [∀ x, NormedSpace ℂ (L x)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L] [IsContinuousNormBundle ℂ L]
  {f : ℂ → B} {σ τ : Π x, L x}

/-!
## Circle integrability of `log ‖σ ∘ f‖`
-/

namespace Bundle

/-- If `σ ∘ f` is analytic in local coordinates, then `log ‖σ (f ·)‖` is circle integrable over
every circle centered at the origin. -/
theorem AnalyticAlong.circleIntegrable_log_norm (h : AnalyticAlong σ f) (r : ℝ) :
    CircleIntegrable (fun z ↦ log ‖σ (f z)‖) 0 r := by
  apply circleIntegrable_of_forall_exists_intervalIntegrable
  intro θ₀
  -- Set up the trivialization at `f (circleMap 0 r θ₀)` and the local data
  set e := trivializationAt ℂ L (f (circleMap 0 r θ₀)) with he_def
  have he : f (circleMap 0 r θ₀) ∈ e.baseSet := mem_baseSet_trivializationAt ℂ L _
  have hg : AnalyticAt ℂ (localCoord e σ ∘ f) (circleMap 0 r θ₀) := h.2 _
  have hG : AnalyticAt ℝ ((localCoord e σ ∘ f) ∘ circleMap 0 r) θ₀ :=
    AnalyticAt.comp (g := localCoord e σ ∘ f) (f := circleMap 0 r) (hg.restrictScalars (𝕜 := ℝ))
      (analyticOnNhd_circleMap 0 r θ₀ (mem_univ _))
  -- Eventually near `θ₀`, `f (circleMap 0 r θ)` lies in the base set and `g` is analytic there
  have h₁ : ∀ᶠ θ in 𝓝 θ₀, f (circleMap 0 r θ) ∈ e.baseSet
      ∧ AnalyticAt ℂ (localCoord e σ ∘ f) (circleMap 0 r θ) :=
    (continuous_circleMap 0 r).continuousAt.eventually
      ((eventually_of_mem (h.1.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he))
        fun _ hw ↦ hw).and hg.eventually_analyticAt)
  -- Dichotomy: either `σ ∘ f` vanishes near `z₀` on the circle, or `g` has an isolated zero
  rcases hG.eventually_eq_zero_or_eventually_ne_zero with h₂ | h₂
  · -- Case 1: `log ‖σ (f ·)‖` vanishes near `θ₀`
    obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.1 (h₁.and h₂)
    refine ⟨ε / 2, by positivity, ContinuousOn.intervalIntegrable ?_⟩
    apply (continuousOn_const (c := (0 : ℝ))).congr
    intro θ hθ
    have hθ' : dist θ θ₀ < ε := by
      rw [uIcc_of_le (by linarith), mem_Icc] at hθ
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    obtain ⟨⟨hmem, -⟩, hzero⟩ := hε' hθ'
    simp only [Function.comp_apply] at hzero
    change log ‖σ (f (circleMap 0 r θ))‖ = 0
    rw [(localCoord_eq_zero_iff (𝕜 := ℂ) e σ hmem).1 hzero]
    simp
  · -- Case 2: `log ‖σ (f ·)‖ = log ‖g ∘ circleMap‖ + log ‖frame‖` away from `θ₀`
    rw [eventually_nhdsWithin_iff] at h₂
    obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.1 (h₁.and h₂)
    refine ⟨ε / 2, by positivity, ?_⟩
    have hball : ∀ θ ∈ [[θ₀ - ε / 2, θ₀ + ε / 2]], dist θ θ₀ < ε := by
      intro θ hθ
      rw [uIcc_of_le (by linarith), mem_Icc] at hθ
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    -- The two summands are interval integrable
    have hI₁ : IntervalIntegrable (fun θ ↦ log ‖localCoord e σ (f (circleMap 0 r θ))‖) volume
        (θ₀ - ε / 2) (θ₀ + ε / 2) := by
      apply MeromorphicOn.intervalIntegrable_log_norm (f := localCoord e σ ∘ f ∘ circleMap 0 r)
      intro θ hθ
      exact (((hε' (hball θ hθ)).1.2.restrictScalars (𝕜 := ℝ)).comp
        (analyticOnNhd_circleMap 0 r θ (mem_univ _))).meromorphicAt
    have hI₂ : IntervalIntegrable (fun θ ↦ log ‖e.symmL ℂ (f (circleMap 0 r θ)) 1‖) volume
        (θ₀ - ε / 2) (θ₀ + ε / 2) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.log
      · exact (e.continuousOn_norm_symmL 1).comp
          (h.1.comp (continuous_circleMap 0 r)).continuousOn
          fun θ hθ ↦ (hε' (hball θ hθ)).1.1
      · intro θ hθ
        exact (e.norm_symmL_pos (hε' (hball θ hθ)).1.1 one_ne_zero).ne'
    -- Patch them together, ignoring the point `θ₀`
    refine (intervalIntegrable_congr_codiscreteWithin ?_).2 (hI₁.add hI₂)
    filter_upwards [self_mem_codiscreteWithin (Ι (θ₀ - ε / 2) (θ₀ + ε / 2)),
      compl_singleton_mem_codiscreteWithin θ₀] with θ hθ hθ'
    obtain ⟨⟨hmem, -⟩, hne⟩ := hε' (hball θ (uIoc_subset_uIcc hθ))
    simp only [Function.comp_apply] at hne
    rw [norm_eq_norm_localCoord_mul e σ hmem, log_mul (norm_ne_zero_iff.2 (hne hθ'))
      (e.norm_symmL_pos hmem one_ne_zero).ne']

/-- If `σ ∘ f` is analytic in local coordinates, then `log ‖σ (f ·)‖⁻¹` is circle integrable over
every circle centered at the origin. -/
theorem AnalyticAlong.circleIntegrable_log_norm_inv (h : AnalyticAlong σ f) (r : ℝ) :
    CircleIntegrable (fun z ↦ log ‖σ (f z)‖⁻¹) 0 r := by
  simpa only [log_inv, Pi.neg_def] using (h.circleIntegrable_log_norm r).neg

end Bundle

/-!
## The proximity function
-/

namespace ValueDistribution

variable (f σ) in
/-- The **proximity function** of a section `σ` of a line bundle with continuous fibre norm along a
map `f : ℂ → B`: the circle average of `log (1 / ‖σ (f ·)‖)`. It measures how close `f` comes to
the zero locus of `σ` on the circle of radius `r`. -/
noncomputable def proximitySection : ℝ → ℝ := circleAverage (fun z ↦ log ‖σ (f z)‖⁻¹) 0

/-- The difference of the proximity functions of two sections `σ`, `τ` of the same line bundle is
the circle average of `log ‖(σ/τ) ∘ f‖`. -/
theorem proximitySection_sub_proximitySection (hσ : AnalyticAlong σ f) (hτ : AnalyticAlong τ f)
    (hσf : ∀ z, sectionOrderAt σ f z ≠ ⊤) (hτf : ∀ z, sectionOrderAt τ f z ≠ ⊤) {r : ℝ}
    (hr : r ≠ 0) :
    proximitySection f τ r - proximitySection f σ r
      = circleAverage (fun z ↦ log ‖sectionRatio ℂ σ τ (f z)‖) 0 r := by
  rw [proximitySection, proximitySection,
    ← circleAverage_fun_sub (hτ.circleIntegrable_log_norm_inv r)
      (hσ.circleIntegrable_log_norm_inv r)]
  apply circleAverage_congr_codiscreteWithin _ hr
  filter_upwards [(hσ.eventually_ne_zero_codiscrete hσf).filter_mono
    (codiscreteWithin_mono (subset_univ _)),
    (hτ.eventually_ne_zero_codiscrete hτf).filter_mono (codiscreteWithin_mono (subset_univ _))]
    with z hz hz'
  have hratio : sectionRatio ℂ σ τ (f z) ≠ 0 := by
    intro h
    apply hz
    rw [← sectionRatio_smul (𝕜 := ℂ) σ τ hz', h, zero_smul]
  rw [log_inv, log_inv, norm_eq_norm_sectionRatio_mul (𝕜 := ℂ) σ τ hz',
    log_mul (norm_ne_zero_iff.2 hratio) (norm_ne_zero_iff.2 hz')]
  ring

/-- If the norm of `σ` is bounded by `C`, the proximity function is bounded below by `-log⁺ C`. -/
theorem neg_posLog_le_proximitySection (h : AnalyticAlong σ f) {C : ℝ} (hC : ∀ x, ‖σ x‖ ≤ C)
    (r : ℝ) :
    -log⁺ C ≤ proximitySection f σ r := by
  rw [proximitySection, ← circleAverage_const (-log⁺ C) 0 r]
  apply circleAverage_mono (circleIntegrable_const _ _ _) (h.circleIntegrable_log_norm_inv r)
  intro z _
  rw [log_inv, neg_le_neg_iff]
  calc log ‖σ (f z)‖
      ≤ log⁺ ‖σ (f z)‖ := by rw [posLog_apply]; exact le_max_right _ _
    _ ≤ log⁺ C := posLog_le_posLog (by linarith [norm_nonneg (σ (f z))]) (hC _)

/-- Over a compact base, the proximity function of a continuous section is bounded from below. -/
theorem exists_le_proximitySection [CompactSpace B] (h : AnalyticAlong σ f)
    (hσ : Continuous (fun x ↦ (σ x : TotalSpace ℂ L))) :
    ∃ c, ∀ r, c ≤ proximitySection f σ r := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_compactSpace hσ
  exact ⟨-log⁺ C, neg_posLog_le_proximitySection h hC⟩

end ValueDistribution
