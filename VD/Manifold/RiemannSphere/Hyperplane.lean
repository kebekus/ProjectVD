/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import VD.Manifold.Bundle.ContinuousNorm
import VD.Manifold.RiemannSphere.Manifold

/-!
# The Hyperplane Bundle `𝒪(1)` on the Riemann Sphere

This file constructs the hyperplane bundle `𝒪(1)` on the Riemann sphere `OnePoint ℂ` as a
holomorphic line bundle with the Fubini–Study norm, together with its sections `θ_a`, `a ∈ ℙ¹`,
vanishing exactly at `a`.

The bundle is given as a `VectorBundleCore` over `OnePoint ℂ` with index set `Bool`: the index
`false` corresponds to the trivialization over `{∞}ᶜ` by the frame `θ_∞`, the index `true` to the
trivialization over `{0}ᶜ` by the frame `θ_0`. On the overlap, `θ_0 = z • θ_∞`, so the coordinate
change from the `θ_∞`-coordinate to the `θ_0`-coordinate is multiplication by `z⁻¹`.

The Fubini–Study norm is defined through an inner product on the fibres,
`⟪v, w⟫ = weight p * conj v * w`, where `weight p = 1 / (1 + ‖z‖ ^ 2)` in the `θ_∞`-coordinate
at `p = z` and `weight ∞ = 1` in the `θ_0`-coordinate at `∞`. Following the construction of
`RiemannianBundle` in Mathlib, the norm is registered on the fibres `hyperplaneBundle p` (which
are definitionally `ℂ`, but carry only the topology from the bundle construction) with
`InnerProductSpace.Core.toNormedAddCommGroupOfTopology`, so that no topology diamond arises. The
identifications between the fibre and `ℂ` are made explicit through `OnePoint.coord` and
`OnePoint.ofCoord`, because instance search does not see through the definition of the fibre.

## Main definitions and results

- `OnePoint.hyperplaneCore`, `OnePoint.hyperplaneBundle`: the line bundle `𝒪(1)`, a `C^ω` vector
  bundle (`OnePoint.hyperplaneCore.instIsContMDiff`) with continuous fibre norm.
- `OnePoint.theta a`: the section of `𝒪(1)` vanishing at `a`, with `OnePoint.contMDiff_theta`,
  `OnePoint.norm_theta_coe_coe : ‖theta a z‖ = ‖z - a‖ / √(1 + ‖z‖ ^ 2)` and
  `OnePoint.norm_theta_infty_coe : ‖theta ∞ z‖ = 1 / √(1 + ‖z‖ ^ 2)`.
-/

open Bundle Filter Function Set Topology
open scoped Manifold

/-- The smoothness exponent `ω` of analytic maps; see `VD/Manifold/RiemannSphere/Manifold.lean`
for why the scope `ContDiff` is not opened. -/
local notation "ω" => (⊤ : WithTop ℕ∞)

namespace OnePoint

/-!
## The bundle
-/

theorem chartCoe_ne_zero {p : OnePoint ℂ} (hp : p ≠ ∞) (hp₀ : p ≠ ((0 : ℂ) : OnePoint ℂ)) :
    chartCoe p ≠ 0 := by
  obtain ⟨z, rfl⟩ := ne_infty_iff_exists.1 hp
  rw [chartCoe_apply_coe]
  exact fun h ↦ hp₀ (by rw [h])

/-- The transition scalars of `𝒪(1)`: `transition i j p` converts the coordinate with respect to
the frame `i` into the coordinate with respect to the frame `j`. -/
noncomputable def transition : Bool → Bool → OnePoint ℂ → ℂ
  | false, true, p => (chartCoe p)⁻¹
  | true, false, p => chartCoe p
  | _, _, _ => 1

@[simp] theorem transition_false_false (p : OnePoint ℂ) : transition false false p = 1 := rfl
@[simp] theorem transition_true_true (p : OnePoint ℂ) : transition true true p = 1 := rfl
@[simp] theorem transition_false_true (p : OnePoint ℂ) :
    transition false true p = (chartCoe p)⁻¹ := rfl
@[simp] theorem transition_true_false (p : OnePoint ℂ) : transition true false p = chartCoe p := rfl

/-- The base sets of the two trivializations of `𝒪(1)`: `{∞}ᶜ` for the frame `θ_∞` (index
`false`) and `{0}ᶜ` for the frame `θ_0` (index `true`). -/
def hyperplaneBaseSet : Bool → Set (OnePoint ℂ)
  | false => {∞}ᶜ
  | true => {((0 : ℂ) : OnePoint ℂ)}ᶜ

@[simp] theorem hyperplaneBaseSet_false : hyperplaneBaseSet false = {∞}ᶜ := rfl

@[simp] theorem hyperplaneBaseSet_true : hyperplaneBaseSet true = {((0 : ℂ) : OnePoint ℂ)}ᶜ := rfl

/-- If `p` lies in the base sets of both trivializations, then `chartCoe p ≠ 0`. -/
theorem chartCoe_ne_zero_of_mem {p : OnePoint ℂ} {i j : Bool} (hi : p ∈ hyperplaneBaseSet i)
    (hj : p ∈ hyperplaneBaseSet j) (hij : i ≠ j) : chartCoe p ≠ 0 := by
  cases i <;> cases j
  · exact absurd rfl hij
  · exact chartCoe_ne_zero hi hj
  · exact chartCoe_ne_zero hj hi
  · exact absurd rfl hij

/-- The index of the preferred trivialization at a point: `true` at `∞`, `false` elsewhere. -/
def hyperplaneIndexAt (p : OnePoint ℂ) : Bool := p.elim true fun _ ↦ false

@[simp] theorem hyperplaneIndexAt_infty : hyperplaneIndexAt ∞ = true := rfl

@[simp] theorem hyperplaneIndexAt_coe (z : ℂ) : hyperplaneIndexAt (z : OnePoint ℂ) = false := rfl

/-- The hyperplane bundle `𝒪(1)` on the Riemann sphere, as a vector bundle core. -/
noncomputable def hyperplaneCore : VectorBundleCore ℂ (OnePoint ℂ) ℂ Bool where
  baseSet := hyperplaneBaseSet
  isOpen_baseSet i := by cases i <;> simp
  indexAt := hyperplaneIndexAt
  mem_baseSet_at p := by induction p using OnePoint.rec <;> simp [hyperplaneIndexAt]
  coordChange i j p := transition i j p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p _ v := by cases i <;> simp
  continuousOn_coordChange i j := by
    have hc : ContinuousOn chartCoe ({∞}ᶜ ∩ {((0 : ℂ) : OnePoint ℂ)}ᶜ) :=
      chartCoe.continuousOn.mono (by simp)
    have hne : ∀ p ∈ ({∞}ᶜ ∩ {((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)), chartCoe p ≠ 0 :=
      fun p hp ↦ chartCoe_ne_zero hp.1 hp.2
    cases i <;> cases j
    · change ContinuousOn (fun p ↦ transition false false p • ContinuousLinearMap.id ℂ ℂ) _
      simp only [transition_false_false, one_smul]
      exact continuousOn_const
    · exact (hc.inv₀ hne).smul continuousOn_const
    · exact (hc.smul continuousOn_const).mono fun p hp ↦ ⟨hp.2, hp.1⟩
    · change ContinuousOn (fun p ↦ transition true true p • ContinuousLinearMap.id ℂ ℂ) _
      simp only [transition_true_true, one_smul]
      exact continuousOn_const
  coordChange_comp i j k p hp v := by
    obtain ⟨⟨hi, hj⟩, hk⟩ := hp
    change transition j k p * (transition i j p * v) = transition i k p * v
    cases i <;> cases j <;> cases k <;> simp only [transition_false_false, transition_true_true,
      transition_false_true, transition_true_false, one_mul] <;>
      first
      | rfl
      | (have := chartCoe_ne_zero_of_mem hi hj (by decide); field_simp)

/-- The hyperplane bundle `𝒪(1)` on the Riemann sphere. The fibres are definitionally `ℂ`, carrying
the coordinate with respect to the frame `θ_∞` at finite points and `θ_0` at `∞`; see `coord` and
`ofCoord`. -/
abbrev hyperplaneBundle : OnePoint ℂ → Type := hyperplaneCore.Fiber

/-- The coordinate of a vector in the fibre of `𝒪(1)` at `p`, with respect to the preferred
trivialization at `p`. -/
def coord {p : OnePoint ℂ} (v : hyperplaneBundle p) : ℂ := v

/-- The vector in the fibre of `𝒪(1)` at `p` with the given coordinate with respect to the
preferred trivialization at `p`. -/
def ofCoord (p : OnePoint ℂ) (c : ℂ) : hyperplaneBundle p := c

@[simp] theorem coord_ofCoord (p : OnePoint ℂ) (c : ℂ) : coord (ofCoord p c) = c := rfl
@[simp] theorem ofCoord_coord {p : OnePoint ℂ} (v : hyperplaneBundle p) : ofCoord p (coord v) = v :=
  rfl
@[simp] theorem coord_zero (p : OnePoint ℂ) : coord (0 : hyperplaneBundle p) = 0 := rfl
@[simp] theorem coord_add {p : OnePoint ℂ} (v w : hyperplaneBundle p) :
    coord (v + w) = coord v + coord w := rfl
@[simp] theorem coord_smul {p : OnePoint ℂ} (r : ℂ) (v : hyperplaneBundle p) :
    coord (r • v) = r * coord v := rfl
theorem coord_eq_zero_iff {p : OnePoint ℂ} {v : hyperplaneBundle p} : coord v = 0 ↔ v = 0 :=
  Iff.rfl
theorem coord_injective (p : OnePoint ℂ) : Injective (coord (p := p)) := fun _ _ h ↦ h

@[simp] theorem hyperplaneCore_baseSet (i : Bool) :
    hyperplaneCore.baseSet i = hyperplaneBaseSet i := rfl

@[simp] theorem hyperplaneCore_indexAt (p : OnePoint ℂ) :
    hyperplaneCore.indexAt p = hyperplaneIndexAt p := rfl

theorem hyperplaneCore_coordChange_apply (i j : Bool) (p : OnePoint ℂ) (v : hyperplaneBundle p) :
    hyperplaneCore.coordChange i j p v = transition i j p * coord v := rfl

/-!
## The Fubini–Study norm
-/

/-- The weight of the Fubini–Study inner product in the preferred coordinate at `p`. -/
noncomputable def weight (p : OnePoint ℂ) : ℝ := p.elim 1 fun z ↦ 1 / (1 + ‖z‖ ^ 2)

@[simp] theorem weight_infty : weight ∞ = 1 := rfl

@[simp] theorem weight_coe (z : ℂ) : weight (z : OnePoint ℂ) = 1 / (1 + ‖z‖ ^ 2) := rfl

theorem weight_pos (p : OnePoint ℂ) : 0 < weight p := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe z => simp only [weight_coe]; positivity

/-- The Fubini–Study inner product on the fibre of `𝒪(1)` at `p`, as an
`InnerProductSpace.Core`. -/
@[instance_reducible]
noncomputable def fiberCore (p : OnePoint ℂ) : InnerProductSpace.Core ℂ (hyperplaneBundle p) where
  inner v w := (weight p : ℂ) * (starRingEnd ℂ (coord v) * coord w)
  conj_inner_symm v w := by simp [mul_comm]
  re_inner_nonneg v := by
    change 0 ≤ Complex.re ((weight p : ℂ) * (starRingEnd ℂ (coord v) * coord v))
    rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg (weight_pos p).le (by positivity)
  add_left v w x := by
    change (weight p : ℂ) * (starRingEnd ℂ (coord (v + w)) * coord x)
      = (weight p : ℂ) * (starRingEnd ℂ (coord v) * coord x)
        + (weight p : ℂ) * (starRingEnd ℂ (coord w) * coord x)
    rw [coord_add, map_add]
    ring
  smul_left v w r := by
    change (weight p : ℂ) * (starRingEnd ℂ (coord (r • v)) * coord w)
      = starRingEnd ℂ r * ((weight p : ℂ) * (starRingEnd ℂ (coord v) * coord w))
    rw [coord_smul, map_mul]
    ring
  definite v hv := by
    change (weight p : ℂ) * (starRingEnd ℂ (coord v) * coord v) = 0 at hv
    rw [Complex.conj_mul', mul_eq_zero, Complex.ofReal_eq_zero] at hv
    rcases hv with h | h
    · exact absurd h (weight_pos p).ne'
    · rw [← coord_eq_zero_iff, ← norm_eq_zero]
      exact pow_eq_zero_iff two_ne_zero |>.1 (Complex.ofReal_eq_zero.1 (by simpa using h))

theorem fiberCore_inner (p : OnePoint ℂ) (v w : hyperplaneBundle p) :
    (fiberCore p).inner v w = (weight p : ℂ) * (starRingEnd ℂ (coord v) * coord w) := rfl

instance (p : OnePoint ℂ) : IsTopologicalAddGroup (hyperplaneBundle p) :=
  inferInstanceAs (IsTopologicalAddGroup ℂ)

instance (p : OnePoint ℂ) : ContinuousConstSMul ℂ (hyperplaneBundle p) :=
  inferInstanceAs (ContinuousConstSMul ℂ ℂ)

theorem continuous_coord (p : OnePoint ℂ) : Continuous (coord (p := p)) := continuous_id

theorem fiberCore_continuousAt (p : OnePoint ℂ) :
    ContinuousAt (fun v : hyperplaneBundle p ↦ (fiberCore p).inner v v) 0 := by
  simp only [fiberCore_inner]
  exact (continuous_const.mul ((Complex.continuous_conj.comp (continuous_coord p)).mul
    (continuous_coord p))).continuousAt

theorem fiberCore_isVonNBounded (p : OnePoint ℂ) :
    Bornology.IsVonNBounded ℂ
      {v : hyperplaneBundle p | RCLike.re ((fiberCore p).inner v v) < 1} := by
  refine (NormedSpace.isVonNBounded_ball ℂ ℂ (√(1 / weight p))).subset ?_
  intro v hv
  have hv' : Complex.re ((weight p : ℂ) * (starRingEnd ℂ (coord v) * coord v)) < 1 := hv
  rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re] at hv'
  rw [Metric.mem_ball, dist_zero_right]
  change ‖coord (p := p) v‖ < √(1 / weight p)
  rw [Real.lt_sqrt (norm_nonneg _), lt_div_iff₀ (weight_pos p), mul_comm]
  exact hv'

/-- The Fubini–Study norm on the fibres of `𝒪(1)`. -/
noncomputable instance (p : OnePoint ℂ) : NormedAddCommGroup (hyperplaneBundle p) :=
  (fiberCore p).toNormedAddCommGroupOfTopology (fiberCore_continuousAt p)
    (fiberCore_isVonNBounded p)

/-- The Fubini–Study inner product on the fibres of `𝒪(1)`. -/
noncomputable instance (p : OnePoint ℂ) : InnerProductSpace ℂ (hyperplaneBundle p) :=
  InnerProductSpace.ofCoreOfTopology (fiberCore p) (fiberCore_continuousAt p)
    (fiberCore_isVonNBounded p)

/-- The Fubini–Study norm of a fibre vector, in terms of its coordinate. -/
theorem norm_eq_sqrt_weight_mul {p : OnePoint ℂ} (v : hyperplaneBundle p) :
    ‖v‖ = √(weight p) * ‖coord v‖ := by
  change √(Complex.re ((fiberCore p).inner v v)) = _
  rw [fiberCore_inner, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, Real.sqrt_mul (weight_pos p).le, Real.sqrt_sq (norm_nonneg _)]

/-- The norm of the frame `i` at `p`, i.e. the factor relating the Fubini–Study norm of a fibre
vector to the absolute value of its coordinate in the trivialization `i`. -/
noncomputable def rho : Bool → OnePoint ℂ → ℝ
  | false, p => 1 / √(1 + ‖chartCoe p‖ ^ 2)
  | true, p => 1 / √(1 + ‖chartInv p‖ ^ 2)

theorem continuousOn_rho (i : Bool) : ContinuousOn (rho i) (hyperplaneBaseSet i) := by
  have hpos : ∀ w : ℂ, √(1 + ‖w‖ ^ 2) ≠ 0 := fun w ↦ (Real.sqrt_pos.2 (by positivity)).ne'
  cases i
  · have : ContinuousOn chartCoe (hyperplaneBaseSet false) := by
      simpa using chartCoe.continuousOn
    exact continuousOn_const.div ((continuousOn_const.add (this.norm.pow 2)).sqrt)
      fun p _ ↦ hpos _
  · have : ContinuousOn chartInv (hyperplaneBaseSet true) := by
      simpa using chartInv.continuousOn
    exact continuousOn_const.div ((continuousOn_const.add (this.norm.pow 2)).sqrt)
      fun p _ ↦ hpos _

/-- In the trivialization `i`, the Fubini–Study norm of a fibre vector is `rho i p` times the
absolute value of its coordinate. -/
theorem norm_eq_rho_mul {i : Bool} {p : OnePoint ℂ} (hp : p ∈ hyperplaneBaseSet i)
    (v : hyperplaneBundle p) :
    ‖v‖ = rho i p * ‖hyperplaneCore.coordChange (hyperplaneIndexAt p) i p v‖ := by
  rw [norm_eq_sqrt_weight_mul, hyperplaneCore_coordChange_apply, norm_mul]
  induction p using OnePoint.rec with
  | infty =>
    cases i
    · simp at hp
    · simp [rho]
  | coe z =>
    cases i
    · simp [rho]
    · have hz : z ≠ 0 := by simpa using hp
      have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
      simp only [rho, hyperplaneIndexAt_coe, transition_false_true, weight_coe,
        chartCoe_apply_coe, chartInv_apply, inv_coe hz, norm_inv, one_div, ← mul_assoc]
      congr 1
      have key : √(1 + ‖z‖⁻¹ ^ 2) * ‖z‖ = √(1 + ‖z‖ ^ 2) := by
        have : 1 + ‖z‖⁻¹ ^ 2 = (1 + ‖z‖ ^ 2) / ‖z‖ ^ 2 := by field_simp; ring
        rw [this, Real.sqrt_div (by positivity), Real.sqrt_sq (norm_nonneg z),
          div_mul_cancel₀ _ hz']
      rw [Real.sqrt_inv, ← key, mul_inv]

/-- The Fubini–Study norm is continuous on the total space of `𝒪(1)`. -/
instance : IsContinuousNormBundle ℂ hyperplaneBundle := by
  refine ⟨continuous_iff_continuousAt.2 fun q₀ ↦ ?_⟩
  set i := hyperplaneIndexAt q₀.1
  set e := hyperplaneCore.localTriv i
  have hq₀ : q₀ ∈ e.source := by
    rw [hyperplaneCore.mem_localTriv_source]
    exact hyperplaneCore.mem_baseSet_at q₀.1
  have h₁ : ContinuousAt (fun q : TotalSpace ℂ hyperplaneBundle ↦ rho i q.1 * ‖(e q).2‖) q₀ := by
    apply ContinuousAt.mul
    · exact ((continuousOn_rho i).continuousAt ((hyperplaneCore.isOpen_baseSet i).mem_nhds
        (hyperplaneCore.mem_baseSet_at q₀.1))).comp hyperplaneCore.continuous_proj.continuousAt
    · exact ((e.continuousOn.continuousAt (e.open_source.mem_nhds hq₀)).snd).norm
  refine h₁.congr ?_
  filter_upwards [e.open_source.mem_nhds hq₀] with q hq
  rw [hyperplaneCore.mem_localTriv_source] at hq
  exact (norm_eq_rho_mul hq q.2).symm

/-!
## Holomorphic structure
-/

/-- The chart `chartCoe` is holomorphic on its source. -/
theorem contMDiffOn_chartCoe : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω chartCoe {∞}ᶜ := by
  have := contMDiffOn_chart (I := 𝓘(ℂ)) (H := ℂ) (M := OnePoint ℂ) (n := ω)
    (x := ((1 : ℂ) : OnePoint ℂ))
  rwa [chartAt_coe, chartCoe_source] at this

/-- The chart `chartInv` is holomorphic on its source. -/
theorem contMDiffOn_chartInv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω chartInv {((0 : ℂ) : OnePoint ℂ)}ᶜ := by
  have := contMDiffOn_chart (I := 𝓘(ℂ)) (H := ℂ) (M := OnePoint ℂ) (n := ω)
    (x := (∞ : OnePoint ℂ))
  rwa [chartAt_infty, chartInv_source] at this

/-- `𝒪(1)` is a holomorphic line bundle: its coordinate changes are analytic. -/
instance hyperplaneCore.instIsContMDiff : hyperplaneCore.IsContMDiff 𝓘(ℂ) ω := by
  refine ⟨fun i j ↦ ?_⟩
  have hc : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω chartCoe ({∞}ᶜ ∩ {((0 : ℂ) : OnePoint ℂ)}ᶜ) :=
    contMDiffOn_chartCoe.mono inter_subset_left
  have hne : ∀ p ∈ ({∞}ᶜ ∩ {((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)), chartCoe p ≠ 0 :=
    fun p hp ↦ chartCoe_ne_zero hp.1 hp.2
  cases i <;> cases j
  · change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω (fun p ↦ transition false false p • _) _
    simp only [transition_false_false, one_smul]
    exact contMDiffOn_const
  · change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun p ↦ (chartCoe p)⁻¹ • ContinuousLinearMap.id ℂ ℂ) ({∞}ᶜ ∩ {((0 : ℂ) : OnePoint ℂ)}ᶜ)
    exact (hc.inv₀ hne).smul contMDiffOn_const
  · change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun p ↦ chartCoe p • ContinuousLinearMap.id ℂ ℂ) ({((0 : ℂ) : OnePoint ℂ)}ᶜ ∩ {∞}ᶜ)
    exact (hc.smul contMDiffOn_const).mono fun p hp ↦ ⟨hp.2, hp.1⟩
  · change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω (fun p ↦ transition true true p • _) _
    simp only [transition_true_true, one_smul]
    exact contMDiffOn_const

/-!
## The sections `θ_a`
-/

/-- The section `θ_a` of `𝒪(1)` vanishing exactly at `a ∈ ℙ¹`. In the coordinate of the frame
`θ_∞` at finite points `z`, it is `z - a` (resp. `1` for `a = ∞`); in the coordinate of the frame
`θ_0` at `∞`, it is `1` (resp. `0` for `a = ∞`). -/
noncomputable def theta (a p : OnePoint ℂ) : hyperplaneBundle p :=
  ofCoord p (a.elim (p.elim 0 fun _ ↦ 1) fun a' ↦ p.elim 1 fun z ↦ z - a')

@[simp] theorem coord_theta_infty_infty : coord (theta ∞ ∞) = 0 := rfl

@[simp] theorem coord_theta_infty_coe (z : ℂ) : coord (theta ∞ (z : OnePoint ℂ)) = 1 := rfl

@[simp] theorem coord_theta_coe_infty (a : ℂ) : coord (theta (a : OnePoint ℂ) ∞) = 1 := rfl

@[simp] theorem coord_theta_coe_coe (a z : ℂ) :
    coord (theta (a : OnePoint ℂ) (z : OnePoint ℂ)) = z - a := rfl

theorem theta_apply_eq_zero_iff {a p : OnePoint ℂ} : theta a p = 0 ↔ p = a := by
  rw [← coord_eq_zero_iff]
  induction a using OnePoint.rec <;> induction p using OnePoint.rec <;> simp [sub_eq_zero]

theorem norm_theta_infty_coe (z : ℂ) : ‖theta ∞ (z : OnePoint ℂ)‖ = 1 / √(1 + ‖z‖ ^ 2) := by
  rw [norm_eq_sqrt_weight_mul, coord_theta_infty_coe, weight_coe,
    Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 1 + ‖z‖ ^ 2)]
  simp

theorem norm_theta_infty_infty : ‖theta ∞ ∞‖ = 0 := by
  rw [norm_eq_sqrt_weight_mul, coord_theta_infty_infty]
  simp

theorem norm_theta_coe_coe (a z : ℂ) :
    ‖theta (a : OnePoint ℂ) (z : OnePoint ℂ)‖ = ‖z - a‖ / √(1 + ‖z‖ ^ 2) := by
  rw [norm_eq_sqrt_weight_mul, coord_theta_coe_coe, weight_coe,
    Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 1 + ‖z‖ ^ 2)]
  simp [div_eq_inv_mul]

theorem norm_theta_coe_infty (a : ℂ) : ‖theta (a : OnePoint ℂ) ∞‖ = 1 := by
  rw [norm_eq_sqrt_weight_mul, coord_theta_coe_infty]
  simp

/-- The sections `θ_a` are holomorphic. -/
theorem contMDiff_theta (a : OnePoint ℂ) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ)) ω (fun p ↦ TotalSpace.mk' ℂ p (theta a p)) := by
  intro p₀
  rw [contMDiffAt_section]
  -- The coordinate of `θ_a` in the trivialization at `p₀`
  change ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
    (fun p ↦ hyperplaneCore.coordChange (hyperplaneIndexAt p) (hyperplaneIndexAt p₀) p
      (theta a p)) p₀
  simp only [hyperplaneCore_coordChange_apply]
  induction p₀ using OnePoint.rec with
  | infty =>
    -- Near `∞`, the coordinate is `1 - a * chartInv p` (resp. `chartInv p` for `a = ∞`)
    have hmem : (∞ : OnePoint ℂ) ∈ ({((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)) := by simp
    have hev : ∀ᶠ p in 𝓝 (∞ : OnePoint ℂ), p ∈ ({((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)) :=
      isOpen_compl_singleton.mem_nhds hmem
    have hinv : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω chartInv ∞ :=
      contMDiffOn_chartInv.contMDiffAt (isOpen_compl_singleton.mem_nhds hmem)
    induction a using OnePoint.rec with
    | infty =>
      refine hinv.congr_of_eventuallyEq ?_
      filter_upwards [hev] with p hp
      induction p using OnePoint.rec with
      | infty => simp
      | coe z =>
        have hz : z ≠ 0 := by simpa using hp
        simp [inv_coe hz]
    | coe a =>
      refine ((contMDiffAt_const (c := (1 : ℂ))).sub
        ((contMDiffAt_const (c := a)).mul hinv)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with p hp
      induction p using OnePoint.rec with
      | infty => simp
      | coe z =>
        have hz : z ≠ 0 := by simpa using hp
        simp only [transition_false_true, hyperplaneIndexAt_coe, hyperplaneIndexAt_infty,
          chartCoe_apply_coe, coord_theta_coe_coe, Pi.mul_apply, chartInv_apply, inv_coe hz]
        rw [mul_sub, inv_mul_cancel₀ hz, mul_comm]
  | coe z₀ =>
    -- Near a finite point, the coordinate is `chartCoe p - a` (resp. `1` for `a = ∞`)
    have hmem : ((z₀ : ℂ) : OnePoint ℂ) ∈ ({∞}ᶜ : Set (OnePoint ℂ)) := by simp
    have hev : ∀ᶠ p in 𝓝 ((z₀ : ℂ) : OnePoint ℂ), p ∈ ({∞}ᶜ : Set (OnePoint ℂ)) :=
      isOpen_compl_singleton.mem_nhds hmem
    have hcoe : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω chartCoe (z₀ : OnePoint ℂ) :=
      contMDiffOn_chartCoe.contMDiffAt (isOpen_compl_singleton.mem_nhds hmem)
    induction a using OnePoint.rec with
    | infty =>
      refine (contMDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with p hp
      obtain ⟨z, rfl⟩ := ne_infty_iff_exists.1 hp
      simp
    | coe a =>
      refine (hcoe.sub (contMDiffAt_const (c := a))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with p hp
      obtain ⟨z, rfl⟩ := ne_infty_iff_exists.1 hp
      simp

end OnePoint
