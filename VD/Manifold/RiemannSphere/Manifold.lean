/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import VD.Manifold.HolomorphicFlat

/-!
# The Riemann Sphere as a Complex Manifold

This file equips the one-point compactification `OnePoint ℂ` of the complex plane, the *Riemann
sphere* `ℙ¹`, with the structure of an analytic manifold modelled on `ℂ`. The atlas consists of
two charts:

- `OnePoint.chartCoe`, the inverse of the open embedding `ℂ → OnePoint ℂ`, defined on `{∞}ᶜ`;
- `OnePoint.chartInv`, the composition of the inversion `OnePoint.inv` (which exchanges `0` and
  `∞` and maps `z` to `z⁻¹`) with `chartCoe`, defined on `{0}ᶜ`.

The transition map is `z ↦ z⁻¹` on `ℂ ∖ {0}`, which is analytic.

## Main results

- `OnePoint.instIsManifold`: `OnePoint ℂ` is an analytic manifold modelled on `ℂ`.
- `OnePoint.contMDiff_coe`: the inclusion `ℂ → OnePoint ℂ` is holomorphic.
- `OnePoint.contMDiff_inv`: the inversion `OnePoint ℂ → OnePoint ℂ` is holomorphic.
- `OnePoint.contMDiffAt_coe_comp_iff`: a map into `OnePoint ℂ` that takes finite values near a
  point is holomorphic there if and only if it is holomorphic as a map into `ℂ`.
-/

open Filter Function Set Topology
open scoped Manifold

/-- The smoothness exponent `ω` of analytic maps. We do not open the scope `ContDiff` here, whose
notation `∞` for `⊤ : ℕ∞ω` clashes with the point `∞` of the Riemann sphere. -/
local notation "ω" => (⊤ : WithTop ℕ∞)

namespace OnePoint

/-!
## Inversion on the Riemann sphere
-/

/-- Inversion on the Riemann sphere: `∞ ↦ 0`, `0 ↦ ∞`, and `z ↦ z⁻¹` for `z ≠ 0`. -/
noncomputable def inv (p : OnePoint ℂ) : OnePoint ℂ :=
  p.elim ((0 : ℂ) : OnePoint ℂ) fun z ↦ if z = 0 then ∞ else ((z⁻¹ : ℂ) : OnePoint ℂ)

@[simp] theorem inv_infty : inv ∞ = ((0 : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem inv_coe_zero : inv ((0 : ℂ) : OnePoint ℂ) = ∞ := by simp [inv]

theorem inv_coe {z : ℂ} (hz : z ≠ 0) : inv (z : OnePoint ℂ) = ((z⁻¹ : ℂ) : OnePoint ℂ) := by
  simp [inv, hz]

@[simp] theorem inv_inv (p : OnePoint ℂ) : inv (inv p) = p := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · simp [hz]
    · rw [inv_coe hz, inv_coe (inv_ne_zero hz), _root_.inv_inv]

theorem inv_involutive : Involutive inv := inv_inv

theorem inv_eq_infty_iff {p : OnePoint ℂ} : inv p = ∞ ↔ p = ((0 : ℂ) : OnePoint ℂ) := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · simp [hz]
    · simp [inv_coe hz, hz]

/-- Inversion is continuous on the Riemann sphere. -/
theorem continuous_inv : Continuous inv := by
  have hfilter : coclosedCompact ℂ = Bornology.cobounded ℂ := by
    rw [coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact]
  rw [continuous_iff]
  constructor
  · -- Behaviour at `∞`: `inv z = z⁻¹ → 0`
    rw [inv_infty, hfilter]
    refine ((continuous_coe.tendsto 0).comp tendsto_inv₀_cobounded).congr' ?_
    filter_upwards [tendsto_inv₀_cobounded'.eventually self_mem_nhdsWithin] with z hz
    simp only [comp_apply, inv_coe (mt inv_eq_zero.2 hz)]
  · -- Continuity on `ℂ`
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · -- At `0`: `inv z = z⁻¹ → ∞`
      subst hz
      rw [ContinuousAt, ← nhdsNE_sup_pure, tendsto_sup]
      refine ⟨?_, tendsto_pure_nhds _ _⟩
      rw [inv_coe_zero]
      refine (tendsto_coe_infty.comp (hfilter ▸ tendsto_inv₀_nhdsNE_zero)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [comp_apply, inv_coe hw]
    · -- Away from `0`: `inv z = z⁻¹` is continuous
      rw [ContinuousAt, inv_coe hz]
      refine ((continuous_coe.tendsto _).comp (tendsto_inv₀ hz)).congr' ?_
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      simp only [comp_apply, inv_coe hw]

/-- Inversion as a homeomorphism of the Riemann sphere. -/
noncomputable def invHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toFun := inv
  invFun := inv
  left_inv := inv_inv
  right_inv := inv_inv
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv

@[simp] theorem invHomeomorph_apply (p : OnePoint ℂ) : invHomeomorph p = inv p := rfl

@[simp] theorem invHomeomorph_symm_apply (p : OnePoint ℂ) : invHomeomorph.symm p = inv p := rfl

/-!
## The two charts
-/

/-- The chart of the Riemann sphere at finite points: the inverse of the open embedding
`ℂ → OnePoint ℂ`, with source `{∞}ᶜ`. -/
noncomputable def chartCoe : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  (isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : ℂ → OnePoint ℂ)).symm

@[simp] theorem chartCoe_source : chartCoe.source = {∞}ᶜ := by
  simp [chartCoe, compl_infty]

@[simp] theorem chartCoe_target : chartCoe.target = univ := by
  simp [chartCoe]

@[simp] theorem chartCoe_apply_coe (z : ℂ) : chartCoe (z : OnePoint ℂ) = z :=
  isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv

@[simp] theorem chartCoe_symm_apply (w : ℂ) : chartCoe.symm w = (w : OnePoint ℂ) := rfl

/-- The chart of the Riemann sphere at infinity: the inversion followed by `chartCoe`, with
source `{0}ᶜ`. -/
noncomputable def chartInv : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  invHomeomorph.toOpenPartialHomeomorph.trans chartCoe

@[simp] theorem chartInv_apply (p : OnePoint ℂ) : chartInv p = chartCoe (inv p) := rfl

@[simp] theorem chartInv_symm_apply (w : ℂ) : chartInv.symm w = inv (w : OnePoint ℂ) := rfl

@[simp] theorem chartInv_source : chartInv.source = {((0 : ℂ) : OnePoint ℂ)}ᶜ := by
  ext p
  simp [chartInv, chartCoe_source, inv_eq_infty_iff]

@[simp] theorem chartInv_target : chartInv.target = univ := by
  simp [chartInv]

/-!
## The manifold structure
-/

/-- The Riemann sphere is a charted space modelled on `ℂ`, with charts `chartCoe` at finite points
and `chartInv` at `∞`. -/
noncomputable instance instChartedSpace : ChartedSpace ℂ (OnePoint ℂ) where
  atlas := {chartCoe, chartInv}
  chartAt p := p.elim chartInv fun _ ↦ chartCoe
  mem_chart_source p := by
    induction p using OnePoint.rec with
    | infty => simp
    | coe z => simp
  chart_mem_atlas p := by
    induction p using OnePoint.rec with
    | infty => simp
    | coe z => simp

@[simp] theorem chartAt_coe (z : ℂ) : chartAt ℂ (z : OnePoint ℂ) = chartCoe := rfl

@[simp] theorem chartAt_infty : chartAt ℂ (∞ : OnePoint ℂ) = chartInv := rfl

theorem mem_atlas_iff {e : OpenPartialHomeomorph (OnePoint ℂ) ℂ} :
    e ∈ atlas ℂ (OnePoint ℂ) ↔ e = chartCoe ∨ e = chartInv := by
  simp [atlas, ChartedSpace.atlas]

/-- The transition map between the two charts is the inversion `z ↦ z⁻¹` on `ℂ ∖ {0}`. -/
theorem contDiffOn_chartCoe_symm_trans_chartInv :
    ContDiffOn ℂ ω (chartCoe.symm ≫ₕ chartInv) (chartCoe.symm ≫ₕ chartInv).source := by
  have hs : (chartCoe.symm ≫ₕ chartInv).source ⊆ {0}ᶜ := by
    intro w hw
    simp only [OpenPartialHomeomorph.trans_source, chartCoe_symm_apply, chartInv_source,
      mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff, coe_eq_coe] at hw
    exact hw.2
  refine ((contDiffOn_inv ℂ).mono hs).congr fun w hw ↦ ?_
  simp [OpenPartialHomeomorph.trans_apply, inv_coe (hs hw)]

/-- The transition map between the two charts is the inversion `z ↦ z⁻¹` on `ℂ ∖ {0}`. -/
theorem contDiffOn_chartInv_symm_trans_chartCoe :
    ContDiffOn ℂ ω (chartInv.symm ≫ₕ chartCoe) (chartInv.symm ≫ₕ chartCoe).source := by
  have hs : (chartInv.symm ≫ₕ chartCoe).source ⊆ {0}ᶜ := by
    intro w hw
    simp only [OpenPartialHomeomorph.trans_source, chartInv_symm_apply, chartCoe_source,
      mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff, inv_eq_infty_iff,
      coe_eq_coe] at hw
    exact hw.2
  refine ((contDiffOn_inv ℂ).mono hs).congr fun w hw ↦ ?_
  simp [OpenPartialHomeomorph.trans_apply, inv_coe (hs hw)]

/-- The Riemann sphere is an analytic manifold modelled on `ℂ`. -/
instance instIsManifold : IsManifold 𝓘(ℂ) ω (OnePoint ℂ) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, CompTriple.comp_eq,
    preimage_id_eq, id_eq, range_id, inter_univ]
  rw [mem_atlas_iff] at he he'
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl
  · exact contDiffOn_id.congr fun w _ ↦ by simp [OpenPartialHomeomorph.trans_apply]
  · exact contDiffOn_chartCoe_symm_trans_chartInv
  · exact contDiffOn_chartInv_symm_trans_chartCoe
  · exact contDiffOn_id.congr fun w _ ↦ by simp [OpenPartialHomeomorph.trans_apply]

/-!
## Holomorphic maps to and from the Riemann sphere
-/

/-- The inclusion `ℂ → OnePoint ℂ` is holomorphic. -/
theorem contMDiff_coe : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((↑) : ℂ → OnePoint ℂ) := by
  intro z
  rw [contMDiffAt_iff_of_mem_source (x := z) (y := (z : OnePoint ℂ)) (by simp) (by simp)]
  refine ⟨continuous_coe.continuousAt, ?_⟩
  simp only [extChartAt, chartAt_coe, chartAt_self_eq, modelWithCornersSelf_coe, range_id]
  refine contDiffWithinAt_id.congr_of_eventuallyEq ?_ (by simp)
  filter_upwards with w
  simp

/-- Inversion is holomorphic on the Riemann sphere. -/
theorem contMDiff_inv : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω inv := by
  intro p
  induction p using OnePoint.rec with
  | infty =>
    rw [contMDiffAt_iff_of_mem_source (x := ∞) (y := inv ∞) (by simp) (by simp)]
    refine ⟨continuous_inv.continuousAt, ?_⟩
    simp only [extChartAt, chartAt_infty, inv_infty, chartAt_coe, modelWithCornersSelf_coe,
      range_id]
    refine contDiffWithinAt_id.congr_of_eventuallyEq ?_ (by simp)
    filter_upwards with w
    simp
  | coe z =>
    by_cases hz : z = 0
    · subst hz
      rw [contMDiffAt_iff_of_mem_source (x := ((0 : ℂ) : OnePoint ℂ)) (y := ∞) (by simp)
        (by simp)]
      refine ⟨continuous_inv.continuousAt, ?_⟩
      simp only [extChartAt, chartAt_infty, chartAt_coe, modelWithCornersSelf_coe, range_id]
      refine contDiffWithinAt_id.congr_of_eventuallyEq ?_ (by simp)
      filter_upwards with w
      simp
    · rw [contMDiffAt_iff_of_mem_source (x := (z : OnePoint ℂ)) (y := ((z⁻¹ : ℂ) : OnePoint ℂ))
        (by simp) (by simp [inv_coe hz])]
      refine ⟨continuous_inv.continuousAt, ?_⟩
      simp only [extChartAt, chartAt_coe, modelWithCornersSelf_coe, range_id,
        contDiffWithinAt_univ]
      have hpt : chartCoe.extend 𝓘(ℂ, ℂ) (z : OnePoint ℂ) = z := by simp
      rw [hpt]
      refine (contDiffAt_inv ℂ hz).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      simp [inv_coe hw]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {g : M → ℂ} {x : M}

/-- A map into `ℂ` is holomorphic at a point if and only if its composition with the inclusion
`ℂ → OnePoint ℂ` is. -/
theorem contMDiffAt_coe_comp_iff :
    ContMDiffAt I 𝓘(ℂ) ω (fun x ↦ (g x : OnePoint ℂ)) x ↔ ContMDiffAt I 𝓘(ℂ) ω g x := by
  refine ⟨fun h ↦ ?_, fun h ↦ (contMDiff_coe (g x)).comp x h⟩
  have hmem : ((g x : ℂ) : OnePoint ℂ) ∈ chartCoe.source := by simp
  have h' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω chartCoe ((g x : OnePoint ℂ)) :=
    (contMDiffOn_chart (x := ((g x : ℂ) : OnePoint ℂ))).contMDiffAt
      (chartCoe.open_source.mem_nhds hmem)
  simpa [comp_def] using h'.comp x h

end OnePoint
