/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import VD.Manifold.SectionDivisor

/-!
# The Counting Function of a Section of a Line Bundle Along a Curve

Let `L` be a line bundle over a manifold `B`, `σ` a section of `L`, and `f : ℂ → B` a holomorphic
map. The *logarithmic counting function* `ValueDistribution.logCountingSection f σ` of value
distribution theory is the logarithmic counting function, in the sense of
`Function.locallyFinsuppWithin.logCounting`, of the divisor `Bundle.sectionDivisor σ f` of the
section `σ ∘ f`. It is a logarithmically weighted count of the points in the disk of radius `r`
that `f` maps into the zero locus of `σ`, with multiplicities.

## Main results

- `ValueDistribution.logCountingSection_nonneg`, `logCountingSection_monotoneOn`: the counting
  function is non-negative for `1 ≤ r` and monotone on `(0, ∞)`.
- `ValueDistribution.logCountingSection_sub_logCountingSection`: the difference of the counting
  functions of two sections `σ`, `τ` of the same line bundle is the counting function of the
  divisor of the meromorphic function `(σ/τ) ∘ f`. Together with Jensen's formula, this is the
  First Main Theorem.
-/

open Bundle Function Set
open scoped ContDiff Manifold

namespace ValueDistribution

variable {B : Type*} [TopologicalSpace B]
  {L : B → Type*} [TopologicalSpace (TotalSpace ℂ L)] [∀ x, NormedAddCommGroup (L x)]
  [∀ x, NormedSpace ℂ (L x)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]
  {f : ℂ → B} {σ τ : Π x, L x}

variable (f σ) in
/-- The **logarithmic counting function** of a section `σ` of a line bundle along a map
`f : ℂ → B`: the logarithmic counting function of the divisor of `σ ∘ f`. -/
noncomputable def logCountingSection : ℝ → ℝ := (sectionDivisor σ f).logCounting

theorem logCountingSection_def :
    logCountingSection f σ = (sectionDivisor σ f).logCounting := rfl

@[simp]
theorem logCountingSection_eval_zero : logCountingSection f σ 0 = 0 :=
  locallyFinsuppWithin.logCounting_eval_zero _

/-- For `1 ≤ r`, the counting function is non-negative. -/
theorem logCountingSection_nonneg {r : ℝ} (hr : 1 ≤ r) : 0 ≤ logCountingSection f σ r :=
  locallyFinsuppWithin.logCounting_nonneg sectionDivisor_nonneg hr

/-- The counting function is monotone on `(0, ∞)`. -/
theorem logCountingSection_monotoneOn : MonotoneOn (logCountingSection f σ) (Ioi 0) :=
  locallyFinsuppWithin.logCounting_mono sectionDivisor_nonneg

section Manifold

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℂ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℂ EB HB} [ChartedSpace HB B]
  [ContMDiffVectorBundle ω ℂ L IB]

/-- The difference of the counting functions of two sections `σ`, `τ` of the same line bundle is
the counting function of the divisor of the meromorphic function `(σ/τ) ∘ f`. -/
theorem logCountingSection_sub_logCountingSection (hf : ContMDiff 𝓘(ℂ) IB ω f)
    (hσ : ContMDiff IB (IB.prod 𝓘(ℂ, ℂ)) ω (fun x ↦ TotalSpace.mk' ℂ x (σ x)))
    (hτ : ContMDiff IB (IB.prod 𝓘(ℂ, ℂ)) ω (fun x ↦ TotalSpace.mk' ℂ x (τ x)))
    (hσf : ∀ z, sectionOrderAt σ f z ≠ ⊤) (hτf : ∀ z, sectionOrderAt τ f z ≠ ⊤) :
    logCountingSection f σ - logCountingSection f τ
      = (MeromorphicOn.divisor (sectionRatio ℂ σ τ ∘ f) univ).logCounting := by
  rw [logCountingSection_def, logCountingSection_def, ← map_sub,
    sectionDivisor_sub_sectionDivisor_eq_divisor_sectionRatio hf hσ hτ hσf hτf]

end Manifold

end ValueDistribution
