/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import VD.Manifold.Bundle.LocalCoord

/-!
# The Divisor of a Section of a Line Bundle Along a Curve

Let `L` be a line bundle over a manifold `B`, `σ` a section of `L`, and `f : 𝕜 → B` a map. This
file defines the *order of vanishing* `Bundle.sectionOrderAt σ f z : ℕ∞` of the pulled-back section
`σ ∘ f` at a point `z`, as the order of the analytic function `localCoord e σ ∘ f`, where `e` is
the trivialization of `L` at `f z`, and the associated *divisor* `Bundle.sectionDivisor σ f`, a
function with locally finite support on `𝕜`.

The relevant regularity hypothesis is encoded in the predicate `Bundle.AnalyticAlong σ f`: `f` is
continuous and `σ ∘ f` is analytic in the trivialization at each point. It is implied by `f` and
`σ` being `C^ω` (`Bundle.ContMDiff.analyticAlong`), but does not mention the manifold structure of
`B`, which is why the divisor can be defined with the junk-value convention that avoids proof
arguments. Following `MeromorphicOn.divisor`, the divisor takes the value `0` at points where the
order is infinite, so that local finiteness holds without any non-degeneracy hypothesis. The
non-degeneracy condition `sectionOrderAt σ f z ≠ ⊤` follows from `∃ z, σ (f z) ≠ 0` when `𝕜` is
preconnected (`Bundle.AnalyticAlong.sectionOrderAt_ne_top`).

## Main results

- `Bundle.sectionOrderAt_eq_analyticOrderAt_localCoord`: the order can be computed with respect to
  any trivialization in the atlas whose base set contains `f z`.
- `Bundle.sectionDivisor_nonneg`: the divisor of a section is effective.
- `Bundle.sectionDivisor_sub_sectionDivisor_eq_divisor_sectionRatio`: the difference of the divisors
  of two sections is the divisor of the meromorphic function `(σ/τ) ∘ f`. This is the input for
  the First Main Theorem, which compares the Nevanlinna functions of two sections of the same line
  bundle by way of Jensen's formula for `(σ/τ) ∘ f`.
-/

open Filter Set Topology
open scoped ContDiff Manifold

namespace Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {L : B → Type*} [TopologicalSpace (TotalSpace 𝕜 L)] [∀ x, NormedAddCommGroup (L x)]
  [∀ x, NormedSpace 𝕜 (L x)] [FiberBundle 𝕜 L] [VectorBundle 𝕜 𝕜 L]
  {σ τ : Π x, L x} {f : 𝕜 → B} {z : 𝕜}

/-!
## Order of vanishing
-/

variable (σ f) in
/-- The order of vanishing of the section `σ ∘ f` at `z`: the order of the analytic function
`localCoord e σ ∘ f` at `z`, where `e` is the trivialization of `L` at `f z`. -/
noncomputable def sectionOrderAt (z : 𝕜) : ℕ∞ :=
  analyticOrderAt (localCoord (trivializationAt 𝕜 L (f z)) σ ∘ f) z

variable (σ f) in
/-- The regularity hypothesis under which the order of vanishing of `σ ∘ f` is well behaved: `f` is
continuous, and `σ ∘ f` is analytic in the trivialization at each point. See
`Bundle.ContMDiff.analyticAlong` for the case of `C^ω` maps and sections. -/
def AnalyticAlong : Prop :=
  Continuous f ∧ ∀ z, AnalyticAt 𝕜 (localCoord (trivializationAt 𝕜 L (f z)) σ ∘ f) z

/-- If `σ (f z) ≠ 0`, the order of vanishing of `σ ∘ f` at `z` is zero. -/
theorem sectionOrderAt_eq_zero_of_ne_zero (h : σ (f z) ≠ 0) : sectionOrderAt σ f z = 0 := by
  apply analyticOrderAt_eq_zero.2 (Or.inr _)
  simpa only [Function.comp_apply, ne_eq,
    localCoord_eq_zero_iff (𝕜 := 𝕜) _ σ (mem_baseSet_trivializationAt 𝕜 L (f z))] using h

/-- If `σ ∘ f` is analytic at `z` in local coordinates, its order of vanishing at `z` is zero if
and only if `σ (f z) ≠ 0`. -/
theorem sectionOrderAt_eq_zero_iff
    (hz : AnalyticAt 𝕜 (localCoord (trivializationAt 𝕜 L (f z)) σ ∘ f) z) :
    sectionOrderAt σ f z = 0 ↔ σ (f z) ≠ 0 := by
  rw [sectionOrderAt, hz.analyticOrderAt_eq_zero, Function.comp_apply]
  exact not_congr (localCoord_eq_zero_iff (𝕜 := 𝕜) _ σ (mem_baseSet_trivializationAt 𝕜 L (f z)))

/-- The order of vanishing of `σ ∘ f` at `z` is infinite if and only if `σ ∘ f` vanishes near
`z`. -/
theorem sectionOrderAt_eq_top_iff (hf : ContinuousAt f z) :
    sectionOrderAt σ f z = ⊤ ↔ ∀ᶠ w in 𝓝 z, σ (f w) = 0 := by
  rw [sectionOrderAt, analyticOrderAt_eq_top]
  apply eventually_congr
  filter_upwards [hf.preimage_mem_nhds
    ((trivializationAt 𝕜 L (f z)).open_baseSet.mem_nhds (mem_baseSet_trivializationAt 𝕜 L (f z)))]
    with w hw
  exact localCoord_eq_zero_iff (𝕜 := 𝕜) _ σ hw

/-- If the order of vanishing of `σ ∘ f` is infinite at `z`, it is infinite near `z`. -/
theorem eventually_sectionOrderAt_eq_top (hf : Continuous f) (h : sectionOrderAt σ f z = ⊤) :
    ∀ᶠ w in 𝓝 z, sectionOrderAt σ f w = ⊤ := by
  filter_upwards [((sectionOrderAt_eq_top_iff hf.continuousAt).1 h).eventually_nhds] with w hw
  exact (sectionOrderAt_eq_top_iff hf.continuousAt).2 hw

/-- If the order of vanishing of `σ ∘ f` at `z` is finite and `σ ∘ f` is analytic at `z` in local
coordinates, then the order of vanishing is zero at all points near `z`, except possibly `z`
itself. -/
theorem eventually_nhdsNE_sectionOrderAt_eq_zero (hf : ContinuousAt f z)
    (hz : AnalyticAt 𝕜 (localCoord (trivializationAt 𝕜 L (f z)) σ ∘ f) z)
    (h : sectionOrderAt σ f z ≠ ⊤) :
    ∀ᶠ w in 𝓝[≠] z, sectionOrderAt σ f w = 0 := by
  rcases hz.eventually_eq_zero_or_eventually_ne_zero with h' | h'
  · exact (h (analyticOrderAt_eq_top.2 h')).elim
  filter_upwards [h', nhdsWithin_le_nhds (hf.preimage_mem_nhds
    ((trivializationAt 𝕜 L (f z)).open_baseSet.mem_nhds (mem_baseSet_trivializationAt 𝕜 L (f z))))]
    with w hw hw'
  apply sectionOrderAt_eq_zero_of_ne_zero
  rwa [Function.comp_apply, ne_eq, localCoord_eq_zero_iff (𝕜 := 𝕜) _ σ hw'] at hw

/-- Over a preconnected field, the order of vanishing of `σ ∘ f` is finite everywhere as soon as
`σ ∘ f` does not vanish identically. -/
theorem AnalyticAlong.sectionOrderAt_ne_top [PreconnectedSpace 𝕜] (h : AnalyticAlong σ f)
    (hne : ∃ z, σ (f z) ≠ 0) (z : 𝕜) : sectionOrderAt σ f z ≠ ⊤ := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hS : IsClopen {z | sectionOrderAt σ f z = ⊤} := by
    constructor
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro w hw
      have := eventually_nhdsNE_sectionOrderAt_eq_zero h.1.continuousAt (h.2 w) hw
      rw [eventually_nhdsWithin_iff] at this
      filter_upwards [this] with v hv
      by_cases hvw : v = w
      · rwa [hvw]
      · simp [hv hvw]
    · rw [isOpen_iff_mem_nhds]
      exact fun w hw ↦ eventually_sectionOrderAt_eq_top h.1 hw
  rcases isClopen_iff.1 hS with hS | hS
  · exact fun hz ↦ (Set.eq_empty_iff_forall_notMem.1 hS) z hz
  · exfalso
    have : sectionOrderAt σ f z₀ = ⊤ := by
      have h := Set.mem_univ z₀
      rwa [← hS] at h
    rw [sectionOrderAt_eq_zero_of_ne_zero hz₀] at this
    exact ENat.zero_ne_top this

/-- If the order of vanishing of `σ ∘ f` is finite everywhere, then `σ ∘ f` vanishes only on a
discrete set. -/
theorem AnalyticAlong.eventually_ne_zero_codiscrete (h : AnalyticAlong σ f)
    (hσf : ∀ z, sectionOrderAt σ f z ≠ ⊤) :
    ∀ᶠ z in codiscrete 𝕜, σ (f z) ≠ 0 := by
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
  intro z
  filter_upwards [eventually_nhdsNE_sectionOrderAt_eq_zero h.1.continuousAt (h.2 z) (hσf z)]
    with w hw
  exact (sectionOrderAt_eq_zero_iff (h.2 w)).1 hw

/-!
## Computing the order with respect to other trivializations
-/

section Manifold

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  [ContMDiffVectorBundle ω 𝕜 L IB]

/-- `C^ω` maps and sections satisfy `AnalyticAlong`. -/
theorem ContMDiff.analyticAlong (hf : ContMDiff 𝓘(𝕜) IB ω f)
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, 𝕜)) ω (fun x ↦ TotalSpace.mk' 𝕜 x (σ x))) :
    AnalyticAlong σ f :=
  ⟨hf.continuous, fun z ↦ ContMDiffAt.analyticAt_localCoord_comp _ σ (hf z) (hσ (f z))
    (mem_baseSet_trivializationAt 𝕜 L (f z))⟩

/-- The order of vanishing of `σ ∘ f` at `z` can be computed with respect to any trivialization in
the atlas whose base set contains `f z`. -/
theorem sectionOrderAt_eq_analyticOrderAt_localCoord (e : Trivialization 𝕜 (π 𝕜 L))
    [MemTrivializationAtlas e] (hf : ContMDiffAt 𝓘(𝕜) IB ω f z)
    (hσ : ContMDiffAt IB (IB.prod 𝓘(𝕜, 𝕜)) ω (fun x ↦ TotalSpace.mk' 𝕜 x (σ x)) (f z))
    (he : f z ∈ e.baseSet) :
    sectionOrderAt σ f z = analyticOrderAt (localCoord e σ ∘ f) z := by
  set e₀ := trivializationAt 𝕜 L (f z)
  have he₀ : f z ∈ e₀.baseSet := mem_baseSet_trivializationAt 𝕜 L (f z)
  have hu := ContMDiffAt.analyticAt_transition_comp e₀ e hf he₀ he
  have hg := ContMDiffAt.analyticAt_localCoord_comp e σ hf hσ he
  calc sectionOrderAt σ f z
      = analyticOrderAt ((localCoord e σ ∘ f) *
          fun w ↦ e₀.continuousLinearMapAt 𝕜 (f w) (e.symmL 𝕜 (f w) 1)) z := by
        apply analyticOrderAt_congr
        filter_upwards [hf.continuousAt.preimage_mem_nhds (e₀.open_baseSet.mem_nhds he₀),
          hf.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)] with w hw₀ hw
        exact localCoord_eq_localCoord_mul e₀ e σ hw₀ hw
    _ = analyticOrderAt (localCoord e σ ∘ f) z := by
        rw [analyticOrderAt_mul hg hu, hu.analyticOrderAt_eq_zero.2
          (continuousLinearMapAt_symmL_one_ne_zero e₀ e he₀ he), add_zero]

end Manifold

/-!
## The divisor
-/

open scoped Classical in
variable (σ f) in
/-- The divisor of the section `σ ∘ f`: the function mapping `z` to the order of vanishing of
`σ ∘ f` at `z`, and to zero if the order is infinite. Takes the value zero everywhere unless
`AnalyticAlong σ f`. -/
noncomputable def sectionDivisor : Function.locallyFinsupp 𝕜 ℤ where
  toFun z := if AnalyticAlong σ f then ((sectionOrderAt σ f z).toNat : ℤ) else 0
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z _ := by
    by_cases h : AnalyticAlong σ f
    · by_cases hz : sectionOrderAt σ f z = ⊤
      · obtain ⟨t, ht, h't⟩ := eventually_iff_exists_mem.1 (eventually_sectionOrderAt_eq_top h.1 hz)
        refine ⟨t, ht, Set.finite_empty.subset fun w ⟨hw, hw'⟩ ↦ hw' ?_⟩
        simp [h, h't w hw]
      · obtain ⟨t, ht, h't⟩ := eventually_iff_exists_mem.1 (eventually_nhdsWithin_iff.1
          (eventually_nhdsNE_sectionOrderAt_eq_zero h.1.continuousAt (h.2 z) hz))
        refine ⟨t, ht, (Set.finite_singleton z).subset fun w ⟨hw, hw'⟩ ↦ ?_⟩
        by_contra hwz
        simp [h, h't w hw hwz] at hw'
    · exact ⟨univ, univ_mem, by simp [h]⟩

open scoped Classical in
theorem sectionDivisor_def :
    sectionDivisor σ f z = if AnalyticAlong σ f then ((sectionOrderAt σ f z).toNat : ℤ) else 0 :=
  rfl

theorem sectionDivisor_apply (h : AnalyticAlong σ f) :
    sectionDivisor σ f z = ((sectionOrderAt σ f z).toNat : ℤ) := by
  simp [sectionDivisor_def, h]

theorem sectionDivisor_of_not (h : ¬ AnalyticAlong σ f) : sectionDivisor σ f = 0 := by
  ext z
  simp [sectionDivisor_def, h]

/-- The divisor of a section is effective. -/
theorem sectionDivisor_nonneg : 0 ≤ sectionDivisor σ f := by
  intro z
  simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sectionDivisor_def]
  split_ifs <;> simp

/-- The divisor of a section vanishes at points where the section does not vanish. -/
theorem sectionDivisor_apply_eq_zero_of_ne_zero (h : σ (f z) ≠ 0) : sectionDivisor σ f z = 0 := by
  simp [sectionDivisor_def, sectionOrderAt_eq_zero_of_ne_zero h]

section Manifold

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  [ContMDiffVectorBundle ω 𝕜 L IB]

/-- The difference of the divisors of two sections `σ`, `τ` of a line bundle along `f` is the
divisor of the meromorphic function `(σ/τ) ∘ f`, provided that neither `σ ∘ f` nor `τ ∘ f`
vanishes identically near any point. -/
theorem sectionDivisor_sub_sectionDivisor_eq_divisor_sectionRatio (hf : ContMDiff 𝓘(𝕜) IB ω f)
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, 𝕜)) ω (fun x ↦ TotalSpace.mk' 𝕜 x (σ x)))
    (hτ : ContMDiff IB (IB.prod 𝓘(𝕜, 𝕜)) ω (fun x ↦ TotalSpace.mk' 𝕜 x (τ x)))
    (hσf : ∀ z, sectionOrderAt σ f z ≠ ⊤) (hτf : ∀ z, sectionOrderAt τ f z ≠ ⊤) :
    sectionDivisor σ f - sectionDivisor τ f
      = MeromorphicOn.divisor (sectionRatio 𝕜 σ τ ∘ f) univ := by
  ext z
  have hσ' := ContMDiff.analyticAlong hf hσ
  have hτ' := ContMDiff.analyticAlong hf hτ
  have he := mem_baseSet_trivializationAt 𝕜 L (f z)
  rw [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, sectionDivisor_apply hσ',
    sectionDivisor_apply hτ', MeromorphicOn.divisor_apply
    (meromorphicOn_univ.2 (ContMDiff.meromorphic_sectionRatio_comp σ τ hf hσ hτ)) (mem_univ z),
    meromorphicOrderAt_congr ((sectionRatio_comp_eventuallyEq (trivializationAt 𝕜 L (f z)) σ τ
      (hf z).continuousAt he).filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_div (hσ'.2 z).meromorphicAt (hτ'.2 z).meromorphicAt,
    (hσ'.2 z).meromorphicOrderAt_eq, (hτ'.2 z).meromorphicOrderAt_eq]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = sectionOrderAt σ f z := ENat.ne_top_iff_exists.1 (hσf z)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℕ∞) = sectionOrderAt τ f z := ENat.ne_top_iff_exists.1 (hτf z)
  unfold sectionOrderAt at hn hm ⊢
  rw [← hn, ← hm]
  simp only [ENat.map_natCast, ENat.toNat_natCast]
  norm_cast

end Manifold

end Bundle
