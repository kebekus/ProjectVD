/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import VD.Manifold.Bundle.ContinuousNorm
import VD.Manifold.HolomorphicFlat

/-!
# Sections of Vector Bundles in Local Coordinates

Given a section `σ` of a vector bundle `E` and a trivialization `e`, the *local coordinate*
`Bundle.localCoord e σ x := (e ⟨x, σ x⟩).2` of `σ` with respect to `e` is a function from the base
to the model fibre. For `x ∈ e.baseSet`, the section is recovered as `σ x = e.symmL 𝕜 x
(localCoord e σ x)`, and `σ` is `C^n` near `x` if and only if `localCoord e σ` is.

For a *line bundle* `L`, i.e. a vector bundle with model fibre the base field `𝕜`, the local
coordinate is a scalar. Two linear trivializations differ by multiplication with a non-vanishing
scalar, so the quotient `Bundle.sectionRatio 𝕜 σ τ := localCoord e σ / localCoord e τ` of the local
coordinates of two sections is independent of the trivialization `e`. It is the meromorphic
function `σ/τ` on the base. Composed with a `C^ω` map `f : 𝕜 → B`, the section ratio is a
meromorphic function on `𝕜`; this is the key to comparing the Nevanlinna functions attached to
different sections of the same line bundle.

## Main definitions and results

- `Bundle.localCoord`: the local coordinate of a section with respect to a trivialization.
- `Bundle.ContMDiffAt.localCoord_comp`, `Bundle.ContMDiffAt.analyticAt_localCoord_comp`: the local
  coordinate of a `C^n` section, composed with a `C^n` map, is `C^n`, resp. analytic.
- `Bundle.norm_eq_norm_localCoord_mul`: `‖σ x‖ = ‖localCoord e σ x‖ * ‖e.symmL 𝕜 x 1‖`.
- `Bundle.sectionRatio`, `Bundle.sectionRatio_eq_div_localCoord`: the section ratio and its
  independence of the trivialization.
- `Bundle.sectionRatio_smul`, `Bundle.norm_eq_norm_sectionRatio_mul`: `σ x = (σ/τ)(x) • τ x`.
- `Bundle.ContMDiffAt.meromorphicAt_sectionRatio_comp`,
  `Bundle.ContMDiff.meromorphic_sectionRatio_comp`: section ratios composed with `C^ω` maps
  `𝕜 → B` are meromorphic.
-/

open Filter Set Topology
open scoped ContDiff Manifold

namespace Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]

/-!
## Local coordinates of sections
-/

section LocalCoord

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace 𝕜 (E x)] [FiberBundle F E]

variable (e : Trivialization F (π F E)) (σ : Π x, E x) {x : B}

/-- The local coordinate of a section `σ` of a vector bundle with respect to a trivialization `e`:
the function `x ↦ (e ⟨x, σ x⟩).2` from the base to the model fibre. It takes junk values outside
`e.baseSet`. -/
def localCoord (x : B) : F := (e ⟨x, σ x⟩).2

omit [∀ x, NormedAddCommGroup (E x)] [FiberBundle F E] in
theorem localCoord_apply : localCoord e σ x = (e ⟨x, σ x⟩).2 := rfl

theorem localCoord_eq_continuousLinearMapAt [e.IsLinear 𝕜] (hx : x ∈ e.baseSet) :
    localCoord e σ x = e.continuousLinearMapAt 𝕜 x (σ x) :=
  (e.continuousLinearMapAt_apply_of_mem 𝕜 hx (σ x)).symm

/-- On `e.baseSet`, a section is recovered from its local coordinate. -/
theorem symmL_localCoord [e.IsLinear 𝕜] (hx : x ∈ e.baseSet) :
    e.symmL 𝕜 x (localCoord e σ x) = σ x := by
  rw [e.symmL_apply hx]
  exact e.symm_apply_apply_mk hx (σ x)

/-- On `e.baseSet`, a section vanishes if and only if its local coordinate does. -/
theorem localCoord_eq_zero_iff [e.IsLinear 𝕜] (hx : x ∈ e.baseSet) :
    localCoord e σ x = 0 ↔ σ x = 0 := by
  constructor
  · intro h
    rw [← symmL_localCoord (𝕜 := 𝕜) e σ hx, h, map_zero]
  · intro h
    rw [localCoord_eq_continuousLinearMapAt (𝕜 := 𝕜) e σ hx, h, map_zero]

section Smoothness

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [VectorBundle 𝕜 F E] [MemTrivializationAtlas e] {f : M → B} {x₀ : M}

/-- The local coordinate of a `C^n` section, composed with a `C^n` map, is `C^n`. -/
theorem ContMDiffAt.localCoord_comp {n : ℕ∞ω} [ContMDiffVectorBundle n F E IB]
    (hf : ContMDiffAt IM IB n f x₀)
    (hσ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (σ x)) (f x₀))
    (he : f x₀ ∈ e.baseSet) :
    ContMDiffAt IM 𝓘(𝕜, F) n (localCoord e σ ∘ f) x₀ :=
  ((e.contMDiffAt_section_iff he).1 hσ).comp x₀ hf

/-- The local coordinate of a `C^ω` section, composed with a `C^ω` map `𝕜 → B`, is analytic. -/
theorem ContMDiffAt.analyticAt_localCoord_comp [ContMDiffVectorBundle ω F E IB] {f : 𝕜 → B}
    {z : 𝕜} (hf : ContMDiffAt 𝓘(𝕜) IB ω f z)
    (hσ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) ω (fun x ↦ TotalSpace.mk' F x (σ x)) (f z))
    (he : f z ∈ e.baseSet) :
    AnalyticAt 𝕜 (localCoord e σ ∘ f) z :=
  (ContMDiffAt.localCoord_comp e σ hf hσ he).analyticAt

end Smoothness

end LocalCoord

/-!
## Line bundles: norms, transition functions and section ratios
-/

section LineBundle

variable {L : B → Type*} [TopologicalSpace (TotalSpace 𝕜 L)] [∀ x, NormedAddCommGroup (L x)]
  [∀ x, NormedSpace 𝕜 (L x)] [FiberBundle 𝕜 L]

variable (e e' : Trivialization 𝕜 (π 𝕜 L)) [e.IsLinear 𝕜] [e'.IsLinear 𝕜] (σ τ : Π x, L x) {x : B}

/-- On `e.baseSet`, a section of a line bundle is the local coordinate times the local frame
`e.symmL 𝕜 x 1`. -/
theorem eq_localCoord_smul_symmL (hx : x ∈ e.baseSet) :
    σ x = localCoord e σ x • e.symmL 𝕜 x 1 := by
  rw [← map_smul, smul_eq_mul, mul_one, symmL_localCoord (𝕜 := 𝕜) e σ hx]

/-- The norm of a section of a line bundle is the norm of its local coordinate times the norm of
the local frame. -/
theorem norm_eq_norm_localCoord_mul (hx : x ∈ e.baseSet) :
    ‖σ x‖ = ‖localCoord e σ x‖ * ‖e.symmL 𝕜 x 1‖ := by
  calc ‖σ x‖
      = ‖localCoord e σ x • e.symmL 𝕜 x 1‖ := by rw [← eq_localCoord_smul_symmL (𝕜 := 𝕜) e σ hx]
    _ = ‖localCoord e σ x‖ * ‖e.symmL 𝕜 x 1‖ := norm_smul _ _

/-- The transition factor between two linear trivializations of a line bundle at a point `x` of
both base sets is non-vanishing. -/
theorem continuousLinearMapAt_symmL_one_ne_zero (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) :
    e.continuousLinearMapAt 𝕜 x (e'.symmL 𝕜 x 1) ≠ 0 := by
  intro h
  apply e'.symmL_ne_zero (𝕜 := 𝕜) hx' one_ne_zero
  rw [← e.symmL_continuousLinearMapAt (R := 𝕜) hx (e'.symmL 𝕜 x 1), h, map_zero]

/-- Local coordinates of a section of a line bundle with respect to two linear trivializations
differ by the transition factor `e.continuousLinearMapAt 𝕜 x (e'.symmL 𝕜 x 1)`. -/
theorem localCoord_eq_localCoord_mul (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) :
    localCoord e σ x = localCoord e' σ x * e.continuousLinearMapAt 𝕜 x (e'.symmL 𝕜 x 1) := by
  rw [localCoord_eq_continuousLinearMapAt (𝕜 := 𝕜) e σ hx]
  conv_lhs => rw [eq_localCoord_smul_symmL (𝕜 := 𝕜) e' σ hx']
  rw [map_smul, smul_eq_mul]

variable [VectorBundle 𝕜 𝕜 L]

variable (𝕜) in
/-- The *section ratio* `σ / τ` of two sections of a line bundle: the quotient of the local
coordinates with respect to the trivialization at the point. By
`Bundle.sectionRatio_eq_div_localCoord`, any linear trivialization whose base set contains the
point gives the same value. -/
noncomputable def sectionRatio (x : B) : 𝕜 :=
  localCoord (trivializationAt 𝕜 L x) σ x / localCoord (trivializationAt 𝕜 L x) τ x

/-- The section ratio can be computed with respect to any linear trivialization whose base set
contains the point. -/
theorem sectionRatio_eq_div_localCoord (hx : x ∈ e.baseSet) :
    sectionRatio 𝕜 σ τ x = localCoord e σ x / localCoord e τ x := by
  have hx' := FiberBundle.mem_baseSet_trivializationAt 𝕜 L x
  unfold sectionRatio
  rw [localCoord_eq_localCoord_mul (trivializationAt 𝕜 L x) e σ hx' hx,
    localCoord_eq_localCoord_mul (trivializationAt 𝕜 L x) e τ hx' hx,
    mul_div_mul_right _ _
      (continuousLinearMapAt_symmL_one_ne_zero (trivializationAt 𝕜 L x) e hx' hx)]

/-- Where `τ` does not vanish, `σ = (σ / τ) • τ`. -/
theorem sectionRatio_smul (hτ : τ x ≠ 0) : sectionRatio 𝕜 σ τ x • τ x = σ x := by
  have hx := FiberBundle.mem_baseSet_trivializationAt 𝕜 L x
  have hτ' : localCoord (trivializationAt 𝕜 L x) τ x ≠ 0 :=
    (not_congr (localCoord_eq_zero_iff (𝕜 := 𝕜) (trivializationAt 𝕜 L x) τ hx)).2 hτ
  calc sectionRatio 𝕜 σ τ x • τ x
      = (localCoord (trivializationAt 𝕜 L x) σ x / localCoord (trivializationAt 𝕜 L x) τ x) •
        (localCoord (trivializationAt 𝕜 L x) τ x • (trivializationAt 𝕜 L x).symmL 𝕜 x 1) := by
        unfold sectionRatio
        rw [← eq_localCoord_smul_symmL (𝕜 := 𝕜) (trivializationAt 𝕜 L x) τ hx]
    _ = localCoord (trivializationAt 𝕜 L x) σ x • (trivializationAt 𝕜 L x).symmL 𝕜 x 1 := by
        rw [smul_smul, div_mul_cancel₀ _ hτ']
    _ = σ x := (eq_localCoord_smul_symmL (trivializationAt 𝕜 L x) σ hx).symm

/-- Where `τ` does not vanish, `‖σ x‖ = ‖(σ / τ)(x)‖ * ‖τ x‖`. -/
theorem norm_eq_norm_sectionRatio_mul (hτ : τ x ≠ 0) :
    ‖σ x‖ = ‖sectionRatio 𝕜 σ τ x‖ * ‖τ x‖ := by
  conv_lhs => rw [← sectionRatio_smul (𝕜 := 𝕜) σ τ hτ]
  exact norm_smul _ _

section Meromorphic

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  [ContMDiffVectorBundle ω 𝕜 L IB] {f : 𝕜 → B} {z : 𝕜}

/-- Near a point `z` where `f z ∈ e.baseSet`, the section ratio composed with `f` is the quotient
of the local coordinates composed with `f`. -/
theorem sectionRatio_comp_eventuallyEq (hf : ContinuousAt f z)
    (he : f z ∈ e.baseSet) :
    sectionRatio 𝕜 σ τ ∘ f =ᶠ[𝓝 z] (localCoord e σ ∘ f) / (localCoord e τ ∘ f) := by
  filter_upwards [hf.preimage_mem_nhds (e.open_baseSet.mem_nhds he)] with w hw
  exact sectionRatio_eq_div_localCoord e σ τ hw

/-- The transition factor `e.continuousLinearMapAt 𝕜 x (e'.symmL 𝕜 x 1)` between two trivializations
of a line bundle in the atlas, composed with a `C^ω` map `f : 𝕜 → B`, is analytic at points `z`
with `f z` in both base sets. -/
theorem ContMDiffAt.analyticAt_transition_comp [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] (hf : ContMDiffAt 𝓘(𝕜) IB ω f z) (he : f z ∈ e.baseSet)
    (he' : f z ∈ e'.baseSet) :
    AnalyticAt 𝕜 (fun w ↦ e.continuousLinearMapAt 𝕜 (f w) (e'.symmL 𝕜 (f w) 1)) z := by
  have h₁ : ContMDiffAt 𝓘(𝕜) 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) ω
      (fun w ↦ (e'.coordChangeL 𝕜 e (f w) : 𝕜 →L[𝕜] 𝕜)) z :=
    ((contMDiffOn_coordChangeL e' e).contMDiffAt
      ((e'.open_baseSet.inter e.open_baseSet).mem_nhds ⟨he', he⟩)).comp z hf
  have h₂ : AnalyticAt 𝕜 (fun w ↦ e'.coordChangeL 𝕜 e (f w) 1) z :=
    (h₁.clm_apply contMDiffAt_const).analyticAt
  refine h₂.congr ?_
  filter_upwards [hf.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he),
    hf.continuousAt.preimage_mem_nhds (e'.open_baseSet.mem_nhds he')] with w hw hw'
  rw [e'.coordChangeL_apply e ⟨hw', hw⟩, e.continuousLinearMapAt_apply_of_mem 𝕜 hw,
    e'.symmL_apply hw']

/-- The section ratio of two `C^ω` sections of a line bundle, composed with a `C^ω` map
`f : 𝕜 → B`, is meromorphic. -/
theorem ContMDiffAt.meromorphicAt_sectionRatio_comp (hf : ContMDiffAt 𝓘(𝕜) IB ω f z)
    (hσ : ContMDiffAt IB (IB.prod 𝓘(𝕜, 𝕜)) ω (fun x ↦ TotalSpace.mk' 𝕜 x (σ x)) (f z))
    (hτ : ContMDiffAt IB (IB.prod 𝓘(𝕜, 𝕜)) ω (fun x ↦ TotalSpace.mk' 𝕜 x (τ x)) (f z)) :
    MeromorphicAt (sectionRatio 𝕜 σ τ ∘ f) z := by
  have he := FiberBundle.mem_baseSet_trivializationAt 𝕜 L (f z)
  refine MeromorphicAt.congr ?_ ((sectionRatio_comp_eventuallyEq (trivializationAt 𝕜 L (f z)) σ τ
    hf.continuousAt he).symm.filter_mono nhdsWithin_le_nhds)
  exact (ContMDiffAt.analyticAt_localCoord_comp (trivializationAt 𝕜 L (f z)) σ hf hσ
    he).meromorphicAt.div
    (ContMDiffAt.analyticAt_localCoord_comp (trivializationAt 𝕜 L (f z)) τ hf hτ he).meromorphicAt

/-- The section ratio of two `C^ω` sections of a line bundle, composed with a `C^ω` map
`f : 𝕜 → B`, is analytic at points where the denominator does not vanish. -/
theorem ContMDiffAt.analyticAt_sectionRatio_comp (hf : ContMDiffAt 𝓘(𝕜) IB ω f z)
    (hσ : ContMDiffAt IB (IB.prod 𝓘(𝕜, 𝕜)) ω (fun x ↦ TotalSpace.mk' 𝕜 x (σ x)) (f z))
    (hτ : ContMDiffAt IB (IB.prod 𝓘(𝕜, 𝕜)) ω (fun x ↦ TotalSpace.mk' 𝕜 x (τ x)) (f z))
    (hτz : τ (f z) ≠ 0) :
    AnalyticAt 𝕜 (sectionRatio 𝕜 σ τ ∘ f) z := by
  have he := FiberBundle.mem_baseSet_trivializationAt 𝕜 L (f z)
  refine AnalyticAt.congr ?_
    (sectionRatio_comp_eventuallyEq (trivializationAt 𝕜 L (f z)) σ τ hf.continuousAt he).symm
  exact (ContMDiffAt.analyticAt_localCoord_comp (trivializationAt 𝕜 L (f z)) σ hf hσ he).div
    (ContMDiffAt.analyticAt_localCoord_comp (trivializationAt 𝕜 L (f z)) τ hf hτ he)
    ((not_congr (localCoord_eq_zero_iff (𝕜 := 𝕜) (trivializationAt 𝕜 L (f z)) τ he)).2 hτz)

/-- The section ratio of two `C^ω` sections of a line bundle, composed with a `C^ω` map
`f : 𝕜 → B`, is meromorphic on `𝕜`. -/
theorem ContMDiff.meromorphic_sectionRatio_comp (hf : ContMDiff 𝓘(𝕜) IB ω f)
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, 𝕜)) ω (fun x ↦ TotalSpace.mk' 𝕜 x (σ x)))
    (hτ : ContMDiff IB (IB.prod 𝓘(𝕜, 𝕜)) ω (fun x ↦ TotalSpace.mk' 𝕜 x (τ x))) :
    Meromorphic (sectionRatio 𝕜 σ τ ∘ f) :=
  fun z ↦ ContMDiffAt.meromorphicAt_sectionRatio_comp σ τ (hf z) (hσ (f z)) (hτ (f z))

end Meromorphic

end LineBundle

end Bundle
