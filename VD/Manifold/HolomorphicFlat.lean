/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Holomorphic Maps Between Normed Spaces, Seen as Manifolds

For maps between normed spaces equipped with their trivial manifold structure, `C^ω`-smoothness in
the sense of manifolds is the same as analyticity, and — over the complex numbers — the same as
differentiability. This file provides the glue lemmas that translate between the manifold notion
`ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') ω f` and the notions `AnalyticAt`, `AnalyticOnNhd` and
`Differentiable` used in the theory of meromorphic functions.

These lemmas are used to read holomorphic maps `ℂ → M` and holomorphic sections of line bundles in
local coordinates, where they become analytic functions of one complex variable.
-/

open Set Topology
open scoped ContDiff Manifold

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {f : E → E'} {x : E}

/-- A `C^ω` map between normed spaces, seen as manifolds, is analytic. -/
theorem ContMDiffAt.analyticAt (h : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') ω f x) : AnalyticAt 𝕜 f x :=
  h.contDiffAt.analyticAt

/-- For maps between normed spaces with values in a complete space, `C^ω` smoothness in the sense
of manifolds is equivalent to analyticity. -/
theorem contMDiffAt_omega_iff_analyticAt [CompleteSpace E'] :
    ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') ω f x ↔ AnalyticAt 𝕜 f x :=
  ⟨fun h ↦ h.analyticAt, fun h ↦ h.contDiffAt.contMDiffAt⟩

/-- For maps between normed spaces, `C^ω` smoothness in the sense of manifolds is equivalent to
analyticity at every point. -/
theorem contMDiff_omega_iff_analyticOnNhd :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') ω f ↔ AnalyticOnNhd 𝕜 f univ := by
  rw [contMDiff_iff_contDiff, contDiff_omega_iff_analyticOnNhd]

end NormedField

/-!
### Maps of one complex variable

Over the complex numbers, `C^ω` smoothness is equivalent to differentiability. The lemmas of this
section are restricted to the source `ℂ` because Mathlib only knows "complex differentiable implies
analytic" in one variable (`Complex.analyticOnNhd_univ_iff_differentiable` and friends, which rest
on the Cauchy integral formula). The statements remain true for maps `E → E'` between complex
normed spaces with `E'` complete, but this requires the theorem that a complex Fréchet
differentiable map on an open subset of a Banach space is analytic (Osgood's lemma / holomorphy in
Banach spaces), which is not yet available in Mathlib.
-/

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}

/-- For maps `ℂ → E` into a complete complex normed space, `C^ω` smoothness in the sense of
manifolds is equivalent to complex differentiability. -/
theorem contMDiff_omega_iff_differentiable :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) ω f ↔ Differentiable ℂ f := by
  rw [contMDiff_omega_iff_analyticOnNhd, Complex.analyticOnNhd_univ_iff_differentiable]

/-- For maps `ℂ → E` into a complete complex normed space, `C^ω` smoothness at a point in the sense
of manifolds is equivalent to complex differentiability near that point. -/
theorem contMDiffAt_omega_iff_eventually_differentiableAt {x : ℂ} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, E) ω f x ↔ ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ f z := by
  rw [contMDiffAt_omega_iff_analyticAt, Complex.analyticAt_iff_eventually_differentiableAt]

end Complex
