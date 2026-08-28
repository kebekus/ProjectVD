/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Vector Bundles with Continuous Fibre Norms

Given a vector bundle whose fibres are all normed spaces, we say that the bundle has a *continuous
norm* if the norm is a continuous function on the total space. This is the minimal structure needed
to speak about the norm `‖σ x‖` of a section `σ` as a continuous function of the base point, which
is all that Nevanlinna theory of holomorphic maps into manifolds requires of a Hermitian metric.

We introduce a typeclass `[IsContinuousNormBundle F E]` registering this property. Under this
assumption, we show that the norm of a continuous map into the fibres of the bundle is a continuous
function, that the norm of the local frame `x ↦ e.symmL 𝕜 x y` given by a linear trivialization `e`
is continuous and non-vanishing on `e.baseSet`, and that norms of continuous sections are bounded
over a compact base.

Continuous Riemannian bundles in the sense of `IsContinuousRiemannianBundle` and trivial bundles
with a normed model fibre have continuous norms.

## Keywords
Vector bundle, Hermitian metric, continuous norm
-/

open Bundle Filter Topology

variable
  {B : Type*} {F : Type*} {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, Norm (E x)]

variable (F E) in
/-- Consider a fibre bundle in which each fibre is endowed with a norm. We say that the bundle has a
*continuous norm* if the norm is a continuous function on the total space. This assumption is
spelled `IsContinuousNormBundle F E` where `F` is the model fibre, and `E : B → Type*` is the
bundle. -/
class IsContinuousNormBundle : Prop where
  /-- The norm is a continuous function on the total space. -/
  continuous_norm : Continuous (fun p : TotalSpace F E ↦ ‖p.2‖)

/-!
## Continuity of norms of maps into the fibres
-/

section Continuous

variable
  {M : Type*} [TopologicalSpace M] [h : IsContinuousNormBundle F E]
  {b : M → B} {v : ∀ x, E (b x)} {s : Set M} {x : M}

/-- Given a continuous map into the fibres of a bundle with continuous norm, its norm is continuous.
Version with `ContinuousWithinAt`. -/
lemma ContinuousWithinAt.norm_bundle
    (hv : ContinuousWithinAt (fun m ↦ (v m : TotalSpace F E)) s x) :
    ContinuousWithinAt (fun m ↦ ‖v m‖) s x :=
  h.continuous_norm.continuousAt.comp_continuousWithinAt hv

/-- Given a continuous map into the fibres of a bundle with continuous norm, its norm is continuous.
Version with `ContinuousAt`. -/
lemma ContinuousAt.norm_bundle (hv : ContinuousAt (fun m ↦ (v m : TotalSpace F E)) x) :
    ContinuousAt (fun m ↦ ‖v m‖) x :=
  h.continuous_norm.continuousAt.comp hv

/-- Given a continuous map into the fibres of a bundle with continuous norm, its norm is continuous.
Version with `ContinuousOn`. -/
lemma ContinuousOn.norm_bundle (hv : ContinuousOn (fun m ↦ (v m : TotalSpace F E)) s) :
    ContinuousOn (fun m ↦ ‖v m‖) s :=
  fun x hx ↦ (hv x hx).norm_bundle

/-- Given a continuous map into the fibres of a bundle with continuous norm, its norm is
continuous. -/
lemma Continuous.norm_bundle (hv : Continuous (fun m ↦ (v m : TotalSpace F E))) :
    Continuous (fun m ↦ ‖v m‖) :=
  h.continuous_norm.comp hv

/-- Over a compact base, the norm of a continuous section of a bundle with continuous norm is
bounded. -/
lemma exists_norm_le_of_compactSpace [TopologicalSpace B] [CompactSpace B] {σ : ∀ x, E x}
    (hσ : Continuous (fun x ↦ (σ x : TotalSpace F E))) :
    ∃ C, ∀ x, ‖σ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_range hσ.norm_bundle).bddAbove
  exact ⟨C, fun x ↦ hC ⟨x, rfl⟩⟩

end Continuous

/-!
## Examples: trivial bundles and Riemannian bundles
-/

section Trivial

variable [TopologicalSpace B] {F₁ : Type*} [NormedAddCommGroup F₁]

/-- A trivial bundle whose model fibre is a normed group has a continuous norm. -/
instance : IsContinuousNormBundle F₁ (Bundle.Trivial B F₁) :=
  ⟨(continuous_snd.comp (Bundle.Trivial.homeomorphProd B F₁).continuous).norm⟩

end Trivial

section Riemannian

variable [TopologicalSpace B]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₂ : B → Type*} [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, NormedAddCommGroup (E₂ x)]
  [∀ x, InnerProductSpace ℝ (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]

/-- A continuous Riemannian bundle has a continuous norm. -/
instance [IsContinuousRiemannianBundle F₂ E₂] : IsContinuousNormBundle F₂ E₂ := by
  refine ⟨?_⟩
  have : Continuous (fun p : TotalSpace F₂ E₂ ↦ inner ℝ p.2 p.2) :=
    Continuous.inner_bundle (b := TotalSpace.proj) (v := fun p ↦ p.2) continuous_id continuous_id
  simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] using this.sqrt

end Riemannian

/-!
## Local frames of linear trivializations
-/

namespace Bundle.Trivialization

variable [TopologicalSpace B]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B → Type*} [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, NormedAddCommGroup (E₃ x)]
  [∀ x, NormedSpace 𝕜 (E₃ x)] [FiberBundle F₃ E₃]
  (e : Trivialization F₃ (π F₃ E₃)) [e.IsLinear 𝕜] {y : F₃} {b : B}

/-- The local frame `x ↦ e.symmL 𝕜 x y` of a linear trivialization `e` is continuous on `e.baseSet`,
as a map into the total space. -/
theorem continuousOn_symmL (y : F₃) :
    ContinuousOn (fun x ↦ (e.symmL 𝕜 x y : TotalSpace F₃ E₃)) e.baseSet := by
  refine (e.continuousOn_symm.comp (Continuous.prodMk_left y).continuousOn ?_).congr ?_
  · exact fun x hx ↦ ⟨hx, Set.mem_univ _⟩
  · exact fun x hx ↦ by simp [e.symmL_apply hx]

/-- The norm of the local frame `x ↦ e.symmL 𝕜 x y` of a linear trivialization `e` is continuous on
`e.baseSet`. -/
theorem continuousOn_norm_symmL [IsContinuousNormBundle F₃ E₃] (y : F₃) :
    ContinuousOn (fun x ↦ ‖e.symmL 𝕜 x y‖) e.baseSet :=
  (e.continuousOn_symmL y).norm_bundle

/-- The local frame `x ↦ e.symmL 𝕜 x y` of a linear trivialization `e` does not vanish on
`e.baseSet` if `y ≠ 0`. -/
theorem symmL_ne_zero (hb : b ∈ e.baseSet) (hy : y ≠ 0) : Trivialization.symmL 𝕜 e b y ≠ 0 := by
  intro h
  apply hy
  rw [← e.continuousLinearMapAt_symmL (R := 𝕜) hb y, h, map_zero]

/-- The norm of the local frame `x ↦ e.symmL 𝕜 x y` of a linear trivialization `e` is positive on
`e.baseSet` if `y ≠ 0`. -/
theorem norm_symmL_pos (hb : b ∈ e.baseSet) (hy : y ≠ 0) : 0 < ‖Trivialization.symmL 𝕜 e b y‖ :=
  norm_pos_iff.mpr (symmL_ne_zero (𝕜 := 𝕜) e hb hy)

end Bundle.Trivialization
