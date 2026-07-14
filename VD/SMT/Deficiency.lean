/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import VD.MathlibPending.BoundednessCharacteristic
import VD.SMT.SecondMainTheorem

/-!
# Deficiency and the Defect Relation — SMT work package G

See `VD/SMT/PLAN-SecondMainTheorem.md`, §9.

Mathlib target: new file `Mathlib/Analysis/Complex/ValueDistribution/Deficiency.lean`.
Dependencies: `VD/SMT/TruncatedCounting.lean` (package A),
`VD/SMT/SecondMainTheorem.lean` (package F); uses the pending
`VD/MathlibPending/BoundednessCharacteristic.lean` for the nonconstancy bridge.

This file defines the **Nevanlinna deficiency** `δ(a)` and the **truncated deficiency**
`Θ(a)` of a value `a ∈ ℂ ∪ {∞}` and proves the **defect relation**: for a transcendental
meromorphic function on `ℂ` and any finite set `S` of targets, `Σ_{a ∈ S} Θ(a) ≤ 2`.
Values with positive deficiency are attained less often than the First Main Theorem
allows; the defect relation asserts that this can happen only for a small set of values.
For the exponential function, which omits the values `0` and `∞`, both deficiencies equal
one and the defect relation is sharp; formalizing this example requires computing
`T(r, exp) = r / π` and is not part of this file.

## Main results

- `ValueDistribution.deficiency` and `ValueDistribution.truncatedDeficiency`: the
  deficiencies `δ(a)` and `Θ(a)`, defined as `liminf`/`limsup` of quotients along `atTop`.

- Basic API, under the hypothesis that the characteristic tends to infinity: the
  deficiencies lie in `[0, 1]`, `δ(a) ≤ Θ(a)`, the First Main Theorem bridge
  `δ(a) = 1 − limsup N(r, a)/T(r)`, and omitted values have deficiency one.

- `ValueDistribution.tendsto_characteristic_atTop_of_not_eventuallyConst`: nonconstant
  meromorphic functions have unbounded characteristic.

- S3, `ValueDistribution.sum_truncatedDeficiency_le`: **the defect relation** for
  transcendental `f` (`Real.log =o[atTop] characteristic f ⊤`), with the corollary
  `ValueDistribution.sum_deficiency_le` for the classical defects `δ(a)`.

The defect relation for *rational* functions is a separate algebraic fact and deliberately
out of scope (see design decision 8 of the plan).

References: [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677], Ch. VII, §3;
[Hayman, *Meromorphic Functions*][MR164038], §2.5; [Noguchi–Winkelmann][MR3156076], §2.3.
-/

open Asymptotics Filter MeasureTheory Metric Real Set Topology

/-!
## The Filter of Large Radii Outside a Set of Finite Measure

The Second Main Theorem holds for all large radii outside a set of finite Lebesgue
measure, that is, along the filter `volume.cofinite ⊓ atTop`.  To extract quantitative
information, we record that this filter is nontrivial: no set of finite measure contains
a neighborhood of infinity.  Flagged for possible upstreaming next to
`MeasureTheory.Measure.cofinite`.
-/

instance : ((volume : Measure ℝ).cofinite ⊓ atTop).NeBot := by
  rw [inf_neBot_iff]
  intro s hs t ht
  obtain ⟨b, hb⟩ := mem_atTop_sets.1 ht
  rcases (s ∩ Set.Ici b).eq_empty_or_nonempty with h | h
  · exfalso
    have h₁ : Set.Ici b ⊆ sᶜ := fun x hx hxs ↦ eq_empty_iff_forall_notMem.1 h x ⟨hxs, hx⟩
    have h₂ := measure_mono (μ := volume) h₁
    rw [Real.volume_Ici] at h₂
    exact absurd (h₂.trans_lt (Measure.mem_cofinite.1 hs)) (lt_irrefl ⊤)
  · obtain ⟨x, hxs, hxb⟩ := h
    exact ⟨x, hxs, hb x hxb⟩

namespace ValueDistribution

/-!
## Definition of the Deficiencies
-/

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/--
The **Nevanlinna deficiency** `δ(a)` of a value `a`: the asymptotic proportion of the
characteristic that stems from the proximity function, i.e. from radii `r` where `f` is
close to `a` on a large portion of the circle `|z| = r`.  Values with positive deficiency
are attained less often than the First Main Theorem allows.
-/
noncomputable def deficiency (f : ℂ → E) (a : WithTop E) : ℝ :=
  liminf (fun r ↦ proximity f a r / characteristic f ⊤ r) atTop

/--
The **truncated deficiency** `Θ(a)` of a value `a`, defined through the truncated counting
function `N̄(r, a)`.  It measures both the deficiency and the asymptotic amount of
ramification of `f` over `a`; the truncated deficiency dominates the Nevanlinna
deficiency, see `ValueDistribution.deficiency_le_truncatedDeficiency`.
-/
noncomputable def truncatedDeficiency (f : ℂ → E) (a : WithTop E) : ℝ :=
  1 - limsup (fun r ↦ truncatedLogCounting f a r / characteristic f ⊤ r) atTop

end Definitions

variable {f : ℂ → ℂ} {a : WithTop ℂ}

/-!
## Elementary Bounds on the Defining Quotients

All bounds below stem from one instance of the (combined) First Main Theorem: for every
value `a`, the characteristic `characteristic f a = m(·, a) + N(·, a)` differs from
`characteristic f ⊤` by a bounded function.
-/

/-- Combined First Main Theorem, uniform over `WithTop ℂ`. -/
private lemma exists_abs_characteristic_sub_le (hf : Meromorphic f) (a : WithTop ℂ) :
    ∃ C, ∀ r, |characteristic f a r - characteristic f ⊤ r| ≤ C := by
  by_cases ha : a = ⊤
  · exact ⟨0, fun r ↦ by simp [ha]⟩
  · lift a to ℂ using ha with a₀
    exact exists_abs_characteristic_coe_sub_characteristic_top_le hf a₀

/-- All three numerators of interest are eventually bounded by `T + C`. -/
private lemma exists_eventually_le_characteristic_add (hf : Meromorphic f) (a : WithTop ℂ) :
    ∃ C, (∀ᶠ r in atTop, proximity f a r ≤ characteristic f ⊤ r + C)
      ∧ (∀ᶠ r in atTop, logCounting f a r ≤ characteristic f ⊤ r + C)
      ∧ ∀ᶠ r in atTop, truncatedLogCounting f a r ≤ characteristic f ⊤ r + C := by
  obtain ⟨C, hC⟩ := exists_abs_characteristic_sub_le hf a
  have h₁ : ∀ᶠ r in atTop, logCounting f a r ≤ characteristic f ⊤ r + C := by
    filter_upwards [eventually_ge_atTop 1] with r hr1
    have h₂ := (abs_le.1 (hC r)).2
    have h₃ : characteristic f a r = proximity f a r + logCounting f a r := rfl
    have h₄ : (0 : ℝ) ≤ proximity f a r := proximity_nonneg r
    linarith
  refine ⟨C, ?_, h₁, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with r hr1
    have h₂ := (abs_le.1 (hC r)).2
    have h₃ : characteristic f a r = proximity f a r + logCounting f a r := rfl
    linarith [logCounting_nonneg (f := f) (e := a) hr1]
  · filter_upwards [h₁, eventually_ge_atTop 1] with r h₁r hr1
    linarith [truncatedLogCounting_le (f := f) (a := a) hr1]

/--
Quotients of eventually nonnegative numerators bounded by `T + C` lie eventually in
`[0, 2]`.  This provides the boundedness and coboundedness side conditions for all
`limsup`/`liminf` manipulations below.
-/
private lemma eventually_div_mem_Icc (hT : Tendsto (characteristic f ⊤) atTop atTop)
    {g : ℝ → ℝ} {C : ℝ} (h₀ : ∀ᶠ r in atTop, 0 ≤ g r)
    (h₁ : ∀ᶠ r in atTop, g r ≤ characteristic f ⊤ r + C) :
    ∀ᶠ r in atTop, g r / characteristic f ⊤ r ∈ Set.Icc 0 2 := by
  filter_upwards [h₀, h₁, hT.eventually_ge_atTop 1, hT.eventually_ge_atTop C]
    with r h₀r h₁r hT1 hTC
  have hTpos : (0 : ℝ) < characteristic f ⊤ r := lt_of_lt_of_le one_pos hT1
  refine ⟨div_nonneg h₀r hTpos.le, ?_⟩
  rw [div_le_iff₀ hTpos]
  linarith

private lemma eventually_proximity_div_mem_Icc (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) (a : WithTop ℂ) :
    ∀ᶠ r in atTop, proximity f a r / characteristic f ⊤ r ∈ Set.Icc 0 2 := by
  obtain ⟨C, h₁, -, -⟩ := exists_eventually_le_characteristic_add hf a
  exact eventually_div_mem_Icc hT (Eventually.of_forall fun r ↦ proximity_nonneg r) h₁

private lemma eventually_logCounting_div_mem_Icc (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) (a : WithTop ℂ) :
    ∀ᶠ r in atTop, logCounting f a r / characteristic f ⊤ r ∈ Set.Icc 0 2 := by
  obtain ⟨C, -, h₁, -⟩ := exists_eventually_le_characteristic_add hf a
  apply eventually_div_mem_Icc hT ?_ h₁
  filter_upwards [eventually_ge_atTop 1] with r hr1
  exact logCounting_nonneg hr1

private lemma eventually_truncatedLogCounting_div_mem_Icc (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) (a : WithTop ℂ) :
    ∀ᶠ r in atTop, truncatedLogCounting f a r / characteristic f ⊤ r ∈ Set.Icc 0 2 := by
  obtain ⟨C, -, -, h₁⟩ := exists_eventually_le_characteristic_add hf a
  apply eventually_div_mem_Icc hT ?_ h₁
  filter_upwards [eventually_ge_atTop 1] with r hr1
  exact truncatedLogCounting_nonneg hr1

/--
The `limsup` of a quotient with numerator eventually `≤ T + C` and eventually nonnegative
is at most one: compare with the function `1 + C/T`, which converges to `1`.
-/
private lemma limsup_div_characteristic_le_one (hT : Tendsto (characteristic f ⊤) atTop atTop)
    {g : ℝ → ℝ} {C : ℝ} (h₀ : ∀ᶠ r in atTop, 0 ≤ g r)
    (h₁ : ∀ᶠ r in atTop, g r ≤ characteristic f ⊤ r + C) :
    limsup (fun r ↦ g r / characteristic f ⊤ r) atTop ≤ 1 := by
  have hv : Tendsto (fun r ↦ 1 + C / characteristic f ⊤ r) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ C) atTop (𝓝 C)).div_atTop hT)
  have hle : ∀ᶠ r in atTop,
      g r / characteristic f ⊤ r ≤ 1 + C / characteristic f ⊤ r := by
    filter_upwards [h₁, hT.eventually_gt_atTop 0] with r h₁r hTpos
    have h₂ : 1 + C / characteristic f ⊤ r
        = (characteristic f ⊤ r + C) / characteristic f ⊤ r := by
      field_simp
    rw [h₂]
    exact (div_le_div_iff_of_pos_right hTpos).2 h₁r
  have hcob : IsCoboundedUnder (· ≤ ·) atTop fun r ↦ g r / characteristic f ⊤ r := by
    apply IsBoundedUnder.isCoboundedUnder_le
    apply isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
    filter_upwards [h₀, hT.eventually_gt_atTop 0] with r h₀r hTpos
    exact div_nonneg h₀r hTpos.le
  calc limsup (fun r ↦ g r / characteristic f ⊤ r) atTop
      ≤ limsup (fun r ↦ 1 + C / characteristic f ⊤ r) atTop :=
        limsup_le_limsup hle hcob hv.isBoundedUnder_le
    _ = 1 := hv.limsup_eq

/-- The relative error of the First Main Theorem vanishes asymptotically. -/
private lemma tendsto_sub_div_nhds_zero (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) (a : WithTop ℂ) :
    Tendsto (fun r ↦ (characteristic f a r - characteristic f ⊤ r) / characteristic f ⊤ r)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_abs_characteristic_sub_le hf a
  have h₁ : Tendsto (fun r ↦ C / characteristic f ⊤ r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hT
  apply squeeze_zero_norm' _ h₁
  filter_upwards [hT.eventually_gt_atTop 0] with r hTpos
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hTpos]
  exact (div_le_div_iff_of_pos_right hTpos).2 (hC r)

/-!
## Elementary Properties of the Deficiencies
-/

/--
The Nevanlinna deficiency is nonnegative for functions with unbounded characteristic.
-/
theorem deficiency_nonneg (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) :
    0 ≤ deficiency f a := by
  apply le_liminf_of_le
  · exact (isBoundedUnder_of_eventually_le
      ((eventually_proximity_div_mem_Icc hf hT a).mono fun r hr ↦ hr.2)).isCoboundedUnder_ge
  · exact (eventually_proximity_div_mem_Icc hf hT a).mono fun r hr ↦ hr.1

/--
The Nevanlinna deficiency is at most one for functions with unbounded characteristic:
by the First Main Theorem, the proximity function cannot asymptotically exceed the
characteristic.
-/
theorem deficiency_le_one (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) :
    deficiency f a ≤ 1 := by
  obtain ⟨C, h₁, -, -⟩ := exists_eventually_le_characteristic_add hf a
  have hIcc := eventually_proximity_div_mem_Icc hf hT a
  calc deficiency f a
      ≤ limsup (fun r ↦ proximity f a r / characteristic f ⊤ r) atTop :=
        liminf_le_limsup (isBoundedUnder_of_eventually_le (hIcc.mono fun r hr ↦ hr.2))
          (isBoundedUnder_of_eventually_ge (hIcc.mono fun r hr ↦ hr.1))
    _ ≤ 1 := limsup_div_characteristic_le_one hT
        (Eventually.of_forall fun r ↦ proximity_nonneg r) h₁

/--
The truncated deficiency is nonnegative for functions with unbounded characteristic:
by the First Main Theorem, the truncated counting function cannot asymptotically exceed
the characteristic.
-/
theorem truncatedDeficiency_nonneg (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) :
    0 ≤ truncatedDeficiency f a := by
  rw [truncatedDeficiency, sub_nonneg]
  obtain ⟨C, -, -, h₁⟩ := exists_eventually_le_characteristic_add hf a
  apply limsup_div_characteristic_le_one hT ?_ h₁
  filter_upwards [eventually_ge_atTop 1] with r hr1
  exact truncatedLogCounting_nonneg hr1

/--
The truncated deficiency is at most one for functions with unbounded characteristic.
-/
theorem truncatedDeficiency_le_one (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) :
    truncatedDeficiency f a ≤ 1 := by
  rw [truncatedDeficiency, sub_le_self_iff]
  apply le_limsup_of_frequently_le
  · apply Eventually.frequently
    exact (eventually_truncatedLogCounting_div_mem_Icc hf hT a).mono fun r hr ↦ hr.1
  · exact isBoundedUnder_of_eventually_le
      ((eventually_truncatedLogCounting_div_mem_Icc hf hT a).mono fun r hr ↦ hr.2)

/--
**First Main Theorem bridge**: for functions with unbounded characteristic, the Nevanlinna
deficiency can be computed through the logarithmic counting function instead of the
proximity function, as `δ(a) = 1 − limsup N(r, a)/T(r)`.
-/
theorem deficiency_eq_one_sub_limsup (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) :
    deficiency f a
      = 1 - limsup (fun r ↦ logCounting f a r / characteristic f ⊤ r) atTop := by
  set u : ℝ → ℝ := fun r ↦ logCounting f a r / characteristic f ⊤ r with hu
  set e : ℝ → ℝ :=
    fun r ↦ (characteristic f a r - characteristic f ⊤ r) / characteristic f ⊤ r with he
  set w : ℝ → ℝ := fun r ↦ 1 - u r with hw
  -- Wherever `T > 0`, the proximity quotient decomposes as `e + w` with `e → 0`.
  have hcongr : (fun r ↦ proximity f a r / characteristic f ⊤ r) =ᶠ[atTop] e + w := by
    filter_upwards [hT.eventually_gt_atTop 0] with r hTpos
    have h₁ : characteristic f a r = proximity f a r + logCounting f a r := rfl
    have hTne : characteristic f ⊤ r ≠ 0 := hTpos.ne'
    simp only [Pi.add_apply, he, hw, hu]
    field_simp
    linarith
  have he₀ : Tendsto e atTop (𝓝 0) := tendsto_sub_div_nhds_zero hf hT a
  -- Boundedness data for the summands.
  have hIccN := eventually_logCounting_div_mem_Icc hf hT a
  have hu_le : IsBoundedUnder (· ≤ ·) atTop u :=
    isBoundedUnder_of_eventually_le (hIccN.mono fun r hr ↦ hr.2)
  have hu_cob : IsCoboundedUnder (· ≤ ·) atTop u :=
    (isBoundedUnder_of_eventually_ge (hIccN.mono fun r hr ↦ hr.1)).isCoboundedUnder_le
  have hw_ge : IsBoundedUnder (· ≥ ·) atTop w := by
    apply isBoundedUnder_of_eventually_ge (a := (-1 : ℝ))
    filter_upwards [hIccN] with r hr
    simp only [hw, hu]
    linarith [hr.2]
  have hw_le : IsBoundedUnder (· ≤ ·) atTop w := by
    apply isBoundedUnder_of_eventually_le (a := (1 : ℝ))
    filter_upwards [hIccN] with r hr
    simp only [hw, hu]
    linarith [hr.1]
  have hw_cob : IsCoboundedUnder (· ≥ ·) atTop w := hw_le.isCoboundedUnder_ge
  have he_ge : IsBoundedUnder (· ≥ ·) atTop e := he₀.isBoundedUnder_ge
  have he_le : IsBoundedUnder (· ≤ ·) atTop e := he₀.isBoundedUnder_le
  -- `liminf w = 1 − limsup u`, and adding the null sequence `e` does not change it.
  have hlimw : liminf w atTop = 1 - limsup u atTop :=
    liminf_const_sub atTop u 1 hu_le hu_cob
  have h₁ : liminf (e + w) atTop ≤ 1 - limsup u atTop := by
    calc liminf (e + w) atTop
        ≤ limsup e atTop + liminf w atTop := liminf_add_le he_ge he_le hw_ge hw_cob
      _ = 1 - limsup u atTop := by rw [he₀.limsup_eq, hlimw, zero_add]
  have h₂ : 1 - limsup u atTop ≤ liminf (e + w) atTop := by
    calc 1 - limsup u atTop
        = liminf e atTop + liminf w atTop := by rw [he₀.liminf_eq, hlimw, zero_add]
      _ ≤ liminf (e + w) atTop := le_liminf_add he_ge he_le hw_ge hw_cob
  rw [deficiency, liminf_congr hcongr]
  exact le_antisymm h₁ h₂

/--
The Nevanlinna deficiency is dominated by the truncated deficiency: dropping
multiplicities can only decrease the counting function.
-/
theorem deficiency_le_truncatedDeficiency (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) :
    deficiency f a ≤ truncatedDeficiency f a := by
  rw [deficiency_eq_one_sub_limsup hf hT, truncatedDeficiency]
  have hle : limsup (fun r ↦ truncatedLogCounting f a r / characteristic f ⊤ r) atTop
      ≤ limsup (fun r ↦ logCounting f a r / characteristic f ⊤ r) atTop := by
    apply limsup_le_limsup
    · filter_upwards [hT.eventually_gt_atTop 0, eventually_ge_atTop 1] with r hTpos hr1
      exact (div_le_div_iff_of_pos_right hTpos).2 (truncatedLogCounting_le hr1)
    · exact (isBoundedUnder_of_eventually_ge
        ((eventually_truncatedLogCounting_div_mem_Icc hf hT a).mono
          fun r hr ↦ hr.1)).isCoboundedUnder_le
    · exact isBoundedUnder_of_eventually_le
        ((eventually_logCounting_div_mem_Icc hf hT a).mono fun r hr ↦ hr.2)
  linarith

/--
Values whose logarithmic counting function vanishes — in particular, omitted values —
have deficiency one.  Package H provides the omission predicate feeding this hypothesis.
-/
theorem deficiency_eq_one_of_logCounting_eq_zero (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) (h : logCounting f a = 0) :
    deficiency f a = 1 := by
  rw [deficiency_eq_one_sub_limsup hf hT]
  have h₁ : (fun r ↦ logCounting f a r / characteristic f ⊤ r) = fun _ ↦ (0 : ℝ) := by
    ext r
    simp [h]
  rw [h₁, limsup_const]
  ring

/-!
## Unbounded Growth of the Characteristic

Two bridges providing the hypothesis `Tendsto (characteristic f ⊤) atTop atTop` used
throughout this file: it holds for transcendental functions (trivially) and, more
generally, for every meromorphic function that is not eventually constant.
-/

/--
Transcendental meromorphic functions — those whose characteristic grows faster than
`log` — have unbounded characteristic.
-/
theorem tendsto_characteristic_atTop_of_log_isLittleO {f : ℂ → ℂ}
    (h : Real.log =o[atTop] characteristic f ⊤) :
    Tendsto (characteristic f ⊤) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [h.def one_pos, eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (max b 0)] with r h₁ h₂ h₃
  have h₄ : 0 ≤ characteristic f ⊤ r := characteristic_nonneg h₂
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg h₄] at h₁
  linarith [le_abs_self (Real.log r), le_max_left b 0]

/--
**Bridge to nonconstancy**: a meromorphic function on `ℂ` that is not eventually constant
has unbounded characteristic.  Combines the boundedness characterization of constant
functions with the monotonicity of the characteristic.
-/
theorem tendsto_characteristic_atTop_of_not_eventuallyConst {f : ℂ → ℂ}
    (hf : Meromorphic f) (h : ¬ EventuallyConst f (codiscrete ℂ)) :
    Tendsto (characteristic f ⊤) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  by_contra hcon
  apply h
  rw [characteristic_isBigO_one_iff_constant (meromorphicOn_univ.2 hf), isBigO_iff]
  rw [not_eventually] at hcon
  refine ⟨|b|, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with r hr
  -- Beyond `r`, some radius `r'` has `T r' < b`; monotonicity bounds `T r` by `T r'`.
  obtain ⟨r', hr'b, hrr'⟩ := (hcon.and_eventually (eventually_ge_atTop r)).exists
  rw [not_le] at hr'b
  have h₀ : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  have hmono := characteristic_monotoneOn hf (mem_Ioi.2 h₀)
    (mem_Ioi.2 (lt_of_lt_of_le h₀ hrr')) hrr'
  have h₁ : 0 ≤ characteristic f ⊤ r := characteristic_nonneg hr
  simp only [Pi.one_apply, norm_one, mul_one, Real.norm_eq_abs]
  rw [abs_of_nonneg h₁]
  linarith [le_abs_self b]

/-!
## The Defect Relation
-/

/--
**Defect relation** (S3): if `f` is meromorphic and transcendental — its characteristic
grows faster than `log` — then, for every finite set `S` of targets in `ℂ ∪ {∞}`, the
truncated deficiencies satisfy `Σ_{a ∈ S} Θ(a) ≤ 2`.  In particular, at most countably
many values have positive deficiency, and the sum of all deficiencies is at most `2`.
-/
theorem sum_truncatedDeficiency_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (h : Real.log =o[atTop] characteristic f ⊤) (S : Finset (WithTop ℂ)) :
    ∑ a ∈ S, truncatedDeficiency f a ≤ 2 := by
  have hT := tendsto_characteristic_atTop_of_log_isLittleO h
  set L : WithTop ℂ → ℝ := fun a ↦
    limsup (fun r ↦ truncatedLogCounting f a r / characteristic f ⊤ r) atTop with hL
  -- Key estimate: `#S − 2 ≤ Σₐ L a`, from the Second Main Theorem after division by `T`.
  have hkey : (S.card : ℝ) - 2 ≤ ∑ a ∈ S, L a := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hq1 : (0 : ℝ) < S.card + 1 := by positivity
    set δ : ℝ := ε / (S.card + 1) with hδ
    have hδpos : 0 < δ := div_pos hε hq1
    -- Each quotient eventually undershoots its `limsup` by less than `δ` …
    have htarget : ∀ a ∈ S, ∀ᶠ r in atTop,
        truncatedLogCounting f a r / characteristic f ⊤ r < L a + δ := by
      intro a _
      exact eventually_lt_of_limsup_lt (lt_add_of_pos_right _ hδpos)
        (isBoundedUnder_of_eventually_le
          ((eventually_truncatedLogCounting_div_mem_Icc hf hT a).mono fun r hr ↦ hr.2))
    -- … and the error term of the Second Main Theorem is eventually below `δ` as well.
    obtain ⟨c, hc⟩ := secondMainTheorem hf S
    have herr : Tendsto (fun r ↦ c * (log⁺ (characteristic f ⊤ r) + Real.log r)
        / characteristic f ⊤ r) (volume.cofinite ⊓ atTop) (𝓝 0) := by
      have h₁ : Tendsto (fun x : ℝ ↦ log⁺ x / x) atTop (𝓝 0) := by
        apply Tendsto.congr' _ Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
        filter_upwards [eventually_ge_atTop 1] with x hx
        rw [Real.posLog_eq_log (by rwa [abs_of_nonneg (by linarith)]), id_eq]
      have h₂ : Tendsto (fun r ↦ log⁺ (characteristic f ⊤ r) / characteristic f ⊤ r)
          atTop (𝓝 0) := h₁.comp hT
      have h₃ : Tendsto (fun r ↦ Real.log r / characteristic f ⊤ r) atTop (𝓝 0) :=
        h.tendsto_div_nhds_zero
      have h₄ := ((h₂.add h₃).const_mul c).mono_left
        (inf_le_right : volume.cofinite ⊓ atTop ≤ atTop)
      simp only [mul_zero, add_zero] at h₄
      apply h₄.congr'
      filter_upwards with r
      rw [mul_div_assoc, add_div]
    -- Pull everything to the filter `volume.cofinite ⊓ atTop` and pick one radius.
    have hev : ∀ᶠ r in volume.cofinite ⊓ atTop,
        (((S.card : ℝ) - 2) * characteristic f ⊤ r
            ≤ ∑ a ∈ S, truncatedLogCounting f a r
              + c * (log⁺ (characteristic f ⊤ r) + Real.log r))
          ∧ (∀ a ∈ S, truncatedLogCounting f a r / characteristic f ⊤ r < L a + δ)
          ∧ c * (log⁺ (characteristic f ⊤ r) + Real.log r) / characteristic f ⊤ r < δ
          ∧ 0 < characteristic f ⊤ r := by
      have h₁ := ((eventually_all_finset S).2 htarget).filter_mono
        (inf_le_right : volume.cofinite ⊓ atTop ≤ atTop)
      have h₂ := herr.eventually_lt_const hδpos
      have h₃ := (hT.eventually_gt_atTop 0).filter_mono
        (inf_le_right : volume.cofinite ⊓ atTop ≤ atTop)
      filter_upwards [hc, h₁, h₂, h₃] with r hr₁ hr₂ hr₃ hr₄
      exact ⟨hr₁, hr₂, hr₃, hr₄⟩
    obtain ⟨r, hr₁, hr₂, hr₃, hr₄⟩ := hev.exists
    -- At this radius: clear denominators and cancel `T r`.
    have h₅ : ∑ a ∈ S, truncatedLogCounting f a r
        ≤ (∑ a ∈ S, L a + S.card * δ) * characteristic f ⊤ r := by
      calc ∑ a ∈ S, truncatedLogCounting f a r
          ≤ ∑ a ∈ S, (L a + δ) * characteristic f ⊤ r :=
            Finset.sum_le_sum fun a ha ↦ le_of_lt ((div_lt_iff₀ hr₄).1 (hr₂ a ha))
        _ = (∑ a ∈ S, L a + S.card * δ) * characteristic f ⊤ r := by
            rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have h₆ : c * (log⁺ (characteristic f ⊤ r) + Real.log r)
        ≤ δ * characteristic f ⊤ r := le_of_lt ((div_lt_iff₀ hr₄).1 hr₃)
    have h₇ : ((S.card : ℝ) - 2) * characteristic f ⊤ r
        ≤ (∑ a ∈ S, L a + ((S.card : ℝ) * δ + δ)) * characteristic f ⊤ r := by
      have h₈ : (∑ a ∈ S, L a + ((S.card : ℝ) * δ + δ)) * characteristic f ⊤ r
          = (∑ a ∈ S, L a + (S.card : ℝ) * δ) * characteristic f ⊤ r
            + δ * characteristic f ⊤ r := by ring
      rw [h₈]
      linarith
    have h₉ := le_of_mul_le_mul_right h₇ hr₄
    have h₁₀ : (S.card : ℝ) * δ + δ = ε := by
      rw [hδ]
      field_simp
    linarith
  -- Rearrange: `Σₐ Θ(a) = #S − Σₐ L a ≤ 2`.
  have hunfold : ∀ a ∈ S, truncatedDeficiency f a = 1 - L a := fun a _ ↦ rfl
  calc ∑ a ∈ S, truncatedDeficiency f a
      = ∑ a ∈ S, (1 - L a) := Finset.sum_congr rfl hunfold
    _ = S.card - ∑ a ∈ S, L a := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 2 := by linarith

/--
**Defect relation**, classical form: if `f` is meromorphic and transcendental, then, for
every finite set `S` of targets in `ℂ ∪ {∞}`, the Nevanlinna deficiencies satisfy
`Σ_{a ∈ S} δ(a) ≤ 2`.
-/
theorem sum_deficiency_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (h : Real.log =o[atTop] characteristic f ⊤) (S : Finset (WithTop ℂ)) :
    ∑ a ∈ S, deficiency f a ≤ 2 := by
  have hT := tendsto_characteristic_atTop_of_log_isLittleO h
  calc ∑ a ∈ S, deficiency f a
      ≤ ∑ a ∈ S, truncatedDeficiency f a :=
        Finset.sum_le_sum fun a _ ↦ deficiency_le_truncatedDeficiency hf hT
    _ ≤ 2 := sum_truncatedDeficiency_le hf h S

end ValueDistribution
