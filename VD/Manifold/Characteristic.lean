/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import VD.Manifold.Counting
import VD.Manifold.Proximity

/-!
# The Characteristic Function of a Section of a Line Bundle Along a Curve

Let `L` be a line bundle with continuous fibre norm over a manifold `B`, `σ` a holomorphic section
of `L`, and `f : ℂ → B` a holomorphic map with `σ ∘ f ≢ 0`. The *Nevanlinna characteristic* (or
*height*) `ValueDistribution.characteristicSection f σ` is the sum of the proximity function and
the logarithmic counting function of `σ` along `f`.

## Main results

- **First Main Theorem**, `ValueDistribution.characteristicSection_sub_characteristicSection`: the
  characteristic functions of two holomorphic sections `σ`, `τ` of the same line bundle differ by
  a constant, namely `-log ‖meromorphicTrailingCoeffAt ((σ/τ) ∘ f) 0‖`. This is an exact identity;
  it follows from Jensen's formula for the meromorphic function `(σ/τ) ∘ f` on `ℂ`. In particular,
  the characteristic function depends on the line bundle only, up to bounded functions.
- **Height functoriality**, `ValueDistribution.characteristic_sectionRatio_le`: the classical
  characteristic `characteristic ((σ/τ) ∘ f) ⊤` of the meromorphic function `(σ/τ) ∘ f` is
  bounded by `characteristicSection f τ` plus a constant, if the sections are bounded.
- **Independence of the metric**, `ValueDistribution.exists_abs_circleAverage_log_comp_le`: two
  continuous fibre norms on a line bundle over a compact base differ by a continuous positive
  factor `ρ`, and the proximity functions then differ by the bounded function
  `circleAverage (log (ρ ∘ f)) 0`.

## References

See Section 2.7 of [Noguchi–Winkelmann, *Nevanlinna theory in several complex variables and
Diophantine approximation*][MR3156076] for the First Main Theorem, and Lemma 4.6 of
Kebekus–Rousseau, *Entire curves in 𝒞-pairs with large irregularity* for the independence of the
metric.
-/

open Bundle Filter Function MeasureTheory Metric Real Set Topology
open scoped ContDiff Manifold

namespace ValueDistribution

variable {B : Type*} [TopologicalSpace B]
  {L : B → Type*} [TopologicalSpace (TotalSpace ℂ L)] [∀ x, NormedAddCommGroup (L x)]
  [∀ x, NormedSpace ℂ (L x)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L] [IsContinuousNormBundle ℂ L]
  {f : ℂ → B} {σ τ : Π x, L x}

variable (f σ) in
/-- The **characteristic function** (or **Nevanlinna height**) of a section `σ` of a line bundle
with continuous fibre norm along a map `f : ℂ → B`: the sum of the proximity function and the
logarithmic counting function. -/
noncomputable def characteristicSection : ℝ → ℝ := proximitySection f σ + logCountingSection f σ

omit [IsContinuousNormBundle ℂ L] in
theorem characteristicSection_def :
    characteristicSection f σ = proximitySection f σ + logCountingSection f σ := rfl

/-!
## Independence of the metric

Two continuous fibre norms `‖·‖₁`, `‖·‖₂` on a line bundle differ by a continuous positive function
`ρ` on the base, `‖v‖₂ = ρ x * ‖v‖₁` for `v` in the fibre over `x`. The proximity functions of a
section with respect to the two norms then differ by `circleAverage (fun z ↦ log (ρ (f z))) 0`,
which is bounded when the base is compact.
-/

/-- Over a compact base, the circle averages of `log (ρ ∘ f)` are uniformly bounded, for every
continuous positive function `ρ` on the base and continuous `f`. -/
theorem exists_abs_circleAverage_log_comp_le [CompactSpace B] (hf : Continuous f) {ρ : B → ℝ}
    (hρ : Continuous ρ) (hρ₀ : ∀ x, 0 < ρ x) :
    ∃ c, ∀ r, |circleAverage (fun z ↦ log (ρ (f z))) 0 r| ≤ c := by
  have hcont : Continuous (fun x ↦ log (ρ x)) := hρ.log fun x ↦ (hρ₀ x).ne'
  obtain ⟨c, hc⟩ := (isCompact_range hcont.norm).bddAbove
  have hc' : ∀ x, |log (ρ x)| ≤ c := fun x ↦ by simpa using hc ⟨x, rfl⟩
  refine ⟨c, fun r ↦ ?_⟩
  have hi : CircleIntegrable (fun z ↦ log (ρ (f z))) 0 r :=
    (hcont.comp hf).continuousOn.circleIntegrable'
  rw [abs_le]
  constructor
  · rw [← circleAverage_const (-c) 0 r]
    exact circleAverage_mono (circleIntegrable_const _ _ _) hi
      fun z _ ↦ (abs_le.1 (hc' (f z))).1
  · exact circleAverage_mono_on_of_le_circle hi fun z _ ↦ (abs_le.1 (hc' (f z))).2

/-!
## The First Main Theorem
-/

section Manifold

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℂ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℂ EB HB} [ChartedSpace HB B]
  [ContMDiffVectorBundle ω ℂ L IB]

/-- **First Main Theorem** for holomorphic maps into manifolds, exact form: the characteristic
functions of two holomorphic sections `σ`, `τ` of the same line bundle along `f` differ by the
constant `-log ‖meromorphicTrailingCoeffAt ((σ/τ) ∘ f) 0‖`. -/
theorem characteristicSection_sub_characteristicSection (hf : ContMDiff 𝓘(ℂ) IB ω f)
    (hσ : ContMDiff IB (IB.prod 𝓘(ℂ, ℂ)) ω (fun x ↦ TotalSpace.mk' ℂ x (σ x)))
    (hτ : ContMDiff IB (IB.prod 𝓘(ℂ, ℂ)) ω (fun x ↦ TotalSpace.mk' ℂ x (τ x)))
    (hσf : ∀ z, sectionOrderAt σ f z ≠ ⊤) (hτf : ∀ z, sectionOrderAt τ f z ≠ ⊤) {R : ℝ}
    (hR : R ≠ 0) :
    characteristicSection f σ R - characteristicSection f τ R
      = -log ‖meromorphicTrailingCoeffAt (sectionRatio ℂ σ τ ∘ f) 0‖ := by
  have hσ' := ContMDiff.analyticAlong hf hσ
  have hτ' := ContMDiff.analyticAlong hf hτ
  have hg : Meromorphic (sectionRatio ℂ σ τ ∘ f) :=
    ContMDiff.meromorphic_sectionRatio_comp σ τ hf hσ hτ
  have h₁ := proximitySection_sub_proximitySection hσ' hτ' hσf hτf hR
  have h₂ := congrFun (logCountingSection_sub_logCountingSection hf hσ hτ hσf hτf) R
  have h₃ := locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const hg hR
  simp only [Pi.sub_apply, comp_apply] at h₂ h₃
  simp only [characteristicSection_def, Pi.add_apply]
  linarith

/-- **First Main Theorem** for holomorphic maps into manifolds, qualitative form: the
characteristic functions of two holomorphic sections of the same line bundle along `f` differ by a
bounded function. -/
theorem isBigO_characteristicSection_sub_characteristicSection (hf : ContMDiff 𝓘(ℂ) IB ω f)
    (hσ : ContMDiff IB (IB.prod 𝓘(ℂ, ℂ)) ω (fun x ↦ TotalSpace.mk' ℂ x (σ x)))
    (hτ : ContMDiff IB (IB.prod 𝓘(ℂ, ℂ)) ω (fun x ↦ TotalSpace.mk' ℂ x (τ x)))
    (hσf : ∀ z, sectionOrderAt σ f z ≠ ⊤) (hτf : ∀ z, sectionOrderAt τ f z ≠ ⊤) :
    (characteristicSection f σ - characteristicSection f τ) =O[atTop] (1 : ℝ → ℝ) := by
  apply Asymptotics.IsBigO.of_bound ‖log ‖meromorphicTrailingCoeffAt (sectionRatio ℂ σ τ ∘ f) 0‖‖
  filter_upwards [eventually_ne_atTop 0] with R hR
  rw [Pi.sub_apply, characteristicSection_sub_characteristicSection hf hσ hτ hσf hτf hR, norm_neg]
  simp

/-!
## Height functoriality
-/

/-- **Height functoriality**: if `σ`, `τ` are holomorphic sections of the same line bundle, with
norms bounded by `C`, then the classical characteristic function of the meromorphic function
`(σ/τ) ∘ f` is bounded by the characteristic function of `τ` along `f`, up to the constant
`2 * log⁺ C`. -/
theorem characteristic_sectionRatio_le (hf : ContMDiff 𝓘(ℂ) IB ω f)
    (hσ : ContMDiff IB (IB.prod 𝓘(ℂ, ℂ)) ω (fun x ↦ TotalSpace.mk' ℂ x (σ x)))
    (hτ : ContMDiff IB (IB.prod 𝓘(ℂ, ℂ)) ω (fun x ↦ TotalSpace.mk' ℂ x (τ x)))
    (hσf : ∀ z, sectionOrderAt σ f z ≠ ⊤) (hτf : ∀ z, sectionOrderAt τ f z ≠ ⊤) {C : ℝ}
    (hσC : ∀ x, ‖σ x‖ ≤ C) (hτC : ∀ x, ‖τ x‖ ≤ C) {r : ℝ} (hr : 1 ≤ r) :
    characteristic (sectionRatio ℂ σ τ ∘ f) ⊤ r ≤ characteristicSection f τ r + 2 * log⁺ C := by
  have hτ' := ContMDiff.analyticAlong hf hτ
  have hg : Meromorphic (sectionRatio ℂ σ τ ∘ f) :=
    ContMDiff.meromorphic_sectionRatio_comp σ τ hf hσ hτ
  -- The counting function of the poles of `(σ/τ) ∘ f` is bounded by the counting function of `τ`
  have hN : logCounting (sectionRatio ℂ σ τ ∘ f) ⊤ r ≤ logCountingSection f τ r := by
    rw [logCounting_top,
      ← sectionDivisor_sub_sectionDivisor_eq_divisor_sectionRatio hf hσ hτ hσf hτf,
      logCountingSection_def]
    apply locallyFinsuppWithin.logCounting_le _ hr
    intro z
    have h₀ : (0 : ℤ) ≤ sectionDivisor σ f z := by
      simpa using sectionDivisor_nonneg (σ := σ) (f := f) z
    have h₀' : (0 : ℤ) ≤ sectionDivisor τ f z := by
      simpa using sectionDivisor_nonneg (σ := τ) (f := f) z
    simp only [locallyFinsuppWithin.negPart_apply, locallyFinsuppWithin.coe_sub, Pi.sub_apply]
    rcases le_total 0 (sectionDivisor σ f z - sectionDivisor τ f z) with h | h
    · rw [negPart_eq_zero.2 h]
      linarith
    · rw [negPart_eq_neg.2 h]
      linarith
  -- The proximity function of `(σ/τ) ∘ f` at `∞` is bounded by the proximity function of `τ`
  have hm : proximity (sectionRatio ℂ σ τ ∘ f) ⊤ r ≤ proximitySection f τ r + 2 * log⁺ C := by
    rw [proximity_top, proximitySection, ← circleAverage_const (2 * log⁺ C) 0 r,
      ← circleAverage_add (hτ'.circleIntegrable_log_norm_inv r) (circleIntegrable_const _ _ _)]
    apply circleAverage_mono (MeromorphicOn.circleIntegrable_posLog_norm (hg.meromorphicOn))
      ((hτ'.circleIntegrable_log_norm_inv r).add (circleIntegrable_const _ _ _))
    intro z _
    simp only [Pi.add_apply, comp_apply]
    have hC : 0 ≤ log⁺ C := posLog_nonneg
    by_cases hz : τ (f z) = 0
    · have : sectionRatio ℂ σ τ (f z) = 0 := by
        rw [sectionRatio_eq_div_localCoord (𝕜 := ℂ) (trivializationAt ℂ L (f z)) σ τ
          (mem_baseSet_trivializationAt ℂ L (f z)),
          (localCoord_eq_zero_iff (𝕜 := ℂ) _ τ (mem_baseSet_trivializationAt ℂ L (f z))).2 hz,
          div_zero]
      simp only [this, hz, norm_zero, posLog_zero, inv_zero, log_zero, zero_add]
      linarith
    · have hnorm : ‖sectionRatio ℂ σ τ (f z)‖ = ‖σ (f z)‖ * ‖τ (f z)‖⁻¹ := by
        rw [norm_eq_norm_sectionRatio_mul (𝕜 := ℂ) σ τ hz]
        field_simp
      have h₁ : log⁺ ‖σ (f z)‖ ≤ log⁺ C :=
        posLog_le_posLog (by linarith [norm_nonneg (σ (f z))]) (hσC _)
      have h₂ : log⁺ ‖τ (f z)‖ ≤ log⁺ C :=
        posLog_le_posLog (by linarith [norm_nonneg (τ (f z))]) (hτC _)
      have h₃ : log⁺ ‖τ (f z)‖ - log⁺ ‖τ (f z)‖⁻¹ = log ‖τ (f z)‖ := posLog_sub_posLog_inv
      have h₄ : log⁺ ‖sectionRatio ℂ σ τ (f z)‖ ≤ log⁺ ‖σ (f z)‖ + log⁺ ‖τ (f z)‖⁻¹ := by
        rw [hnorm]
        exact posLog_mul
      rw [log_inv]
      linarith
  have : characteristic (sectionRatio ℂ σ τ ∘ f) ⊤ r
      = proximity (sectionRatio ℂ σ τ ∘ f) ⊤ r + logCounting (sectionRatio ℂ σ τ ∘ f) ⊤ r := rfl
  rw [this, characteristicSection_def, Pi.add_apply]
  linarith

end Manifold

end ValueDistribution
