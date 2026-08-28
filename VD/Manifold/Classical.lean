/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import VD.Manifold.Characteristic
import VD.Manifold.RiemannSphere.Hyperplane
import VD.Manifold.RiemannSphere.OfMeromorphic

/-!
# Comparison with the Classical Nevanlinna Functions

A meromorphic function `f : ℂ → ℂ` extends to a holomorphic map `F := toRiemannSphere f` into
the Riemann sphere. This file compares the Nevanlinna functions of the section `θ_a` of the
hyperplane bundle `𝒪(1)` along `F` with the classical Nevanlinna functions of `f` for the value
`a ∈ ℂ ∪ {∞}`, as defined in `Mathlib/Analysis/Complex/ValueDistribution/`.

## Main results

- `ValueDistribution.logCountingSection_theta_infty`, `logCountingSection_theta_coe`: the counting
  functions agree **exactly**, because the divisor of `θ_a ∘ F` is the divisor of zeros of `f - a`
  (resp. the divisor of poles of `f`).
- `ValueDistribution.abs_proximitySection_theta_infty_sub_proximity_le`,
  `abs_proximitySection_theta_coe_sub_proximity_le`: the proximity functions agree up to the
  explicit constants `log 2 / 2`, resp. `log 2 / 2 + log 2 + log⁺ ‖a‖`. The discrepancy comes from
  the Fubini–Study metric: `log (1 / ‖θ_∞ (F z)‖) = log (1 + ‖f z‖ ^ 2) / 2`, while the classical
  proximity function uses `log⁺ ‖f z‖`, and `0 ≤ log (1 + x ^ 2) / 2 - log⁺ x ≤ log 2 / 2`.
- `ValueDistribution.abs_characteristicSection_theta_infty_sub_characteristic_le`,
  `abs_characteristicSection_theta_coe_sub_characteristic_le`: consequently, the characteristic
  functions agree up to the same constants.
-/

open Bundle Filter Function MeasureTheory Metric OnePoint Real Set Topology
open scoped Manifold

/-- The smoothness exponent `ω` of analytic maps; see `VD/Manifold/RiemannSphere/Manifold.lean`
for why the scope `ContDiff` is not opened. -/
local notation "ω" => (⊤ : WithTop ℕ∞)

namespace ValueDistribution

variable {f : ℂ → ℂ}

/-!
## Elementary inequalities
-/

/-- The Fubini–Study proximity term `log (1 + x ^ 2) / 2` differs from `log⁺ x` by at most
`log 2 / 2`. -/
theorem abs_log_one_add_sq_div_two_sub_posLog_le {x : ℝ} (hx : 0 ≤ x) :
    |log (1 + x ^ 2) / 2 - log⁺ x| ≤ log 2 / 2 := by
  rw [posLog_eq_log_max_one hx, abs_le]
  have h₁ : (0 : ℝ) < max 1 x := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hlow : (max 1 x) ^ 2 ≤ 1 + x ^ 2 := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; nlinarith
  have hup : 1 + x ^ 2 ≤ 2 * (max 1 x) ^ 2 := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have e₁ := log_le_log (by positivity) hlow
  have e₂ := log_le_log (by positivity) hup
  rw [log_pow] at e₁
  rw [log_mul (by norm_num) (by positivity), log_pow] at e₂
  push_cast at e₁ e₂
  constructor <;> linarith

/-- Shifting the argument of `log⁺ ‖·‖` by `a` changes it by at most `log 2 + log⁺ ‖a‖`. -/
theorem abs_posLog_norm_sub_posLog_norm_sub_le (w a : ℂ) :
    |log⁺ ‖w‖ - log⁺ ‖w - a‖| ≤ log 2 + log⁺ ‖a‖ := by
  rw [abs_le]
  have h₁ : log⁺ ‖w‖ ≤ log 2 + log⁺ ‖w - a‖ + log⁺ ‖a‖ := by
    calc log⁺ ‖w‖ = log⁺ ‖(w - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ log⁺ (‖w - a‖ + ‖a‖) :=
          posLog_le_posLog (by linarith [norm_nonneg ((w - a) + a)]) (norm_add_le _ _)
      _ ≤ log 2 + log⁺ ‖w - a‖ + log⁺ ‖a‖ := posLog_add
  have h₂ : log⁺ ‖w - a‖ ≤ log 2 + log⁺ ‖w‖ + log⁺ ‖a‖ := by
    calc log⁺ ‖w - a‖ ≤ log⁺ (‖w‖ + ‖a‖) :=
          posLog_le_posLog (by linarith [norm_nonneg (w - a)]) (norm_sub_le _ _)
      _ ≤ log 2 + log⁺ ‖w‖ + log⁺ ‖a‖ := posLog_add
  constructor <;> linarith

/-!
## The sections `θ_a` along `toRiemannSphere f`
-/

/-- The sections `θ_a` are analytic along the extension of a meromorphic function to the Riemann
sphere. -/
theorem _root_.Meromorphic.analyticAlong_theta (hf : Meromorphic f) (a : OnePoint ℂ) :
    AnalyticAlong (theta a) (toRiemannSphere f) :=
  ContMDiff.analyticAlong hf.contMDiff_toRiemannSphere (contMDiff_theta a)

/-- A meromorphic function has a point that is not a pole. -/
theorem _root_.Meromorphic.exists_toRiemannSphere_ne_infty (hf : Meromorphic f) :
    ∃ z, toRiemannSphere f z ≠ ∞ := by
  obtain ⟨z, hz⟩ := (hf 0).eventually_analyticAt.exists
  refine ⟨z, ?_⟩
  rw [ne_eq, toRiemannSphere_eq_infty_iff, not_lt]
  exact hz.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.2 hz

/-- If the extension of `f` to the Riemann sphere is not identically `a`, then `θ_a ∘ F` has
finite order of vanishing everywhere. -/
theorem _root_.Meromorphic.sectionOrderAt_theta_ne_top (hf : Meromorphic f) {a : OnePoint ℂ}
    (ha : ∃ z, toRiemannSphere f z ≠ a) (z : ℂ) :
    sectionOrderAt (theta a) (toRiemannSphere f) z ≠ ⊤ := by
  apply (hf.analyticAlong_theta a).sectionOrderAt_ne_top _ z
  obtain ⟨z, hz⟩ := ha
  exact ⟨z, mt theta_apply_eq_zero_iff.1 hz⟩

/-- The section ratio of two sections of `𝒪(1)` is the quotient of their coordinates. -/
theorem _root_.OnePoint.sectionRatio_eq_coord_div (σ τ : Π p, hyperplaneBundle p) (p : OnePoint ℂ) :
    sectionRatio ℂ σ τ p = coord (σ p) / coord (τ p) := by
  have h : ∀ ρ : Π p, hyperplaneBundle p,
      localCoord (trivializationAt ℂ hyperplaneBundle p) ρ p = coord (ρ p) := by
    intro ρ
    change (hyperplaneCore.localTrivAt p ⟨p, ρ p⟩).2 = coord (ρ p)
    rw [← hyperplaneCore.localTrivAt_def, VectorBundleCore.localTriv_apply]
    exact hyperplaneCore.coordChange_self _ _ (hyperplaneCore.mem_baseSet_at p) _
  rw [sectionRatio, h, h]

/-- Away from a discrete set, the section ratio `θ_a / θ_∞` along `F` is `f - a`. -/
theorem _root_.Meromorphic.sectionRatio_theta_comp_eventuallyEq (hf : Meromorphic f) (a : ℂ) :
    (sectionRatio ℂ (theta a) (theta ∞) ∘ toRiemannSphere f) =ᶠ[codiscrete ℂ] (f · - a) := by
  filter_upwards [hf.toRiemannSphere_eventuallyEq_coe] with z hz
  simp [comp_apply, hz, sectionRatio_eq_coord_div]

/-!
## Divisors
-/

/-- Uniqueness of the Jordan decomposition of an integer. -/
theorem posPart_eq_and_negPart_eq_of_eq_sub {a b d : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a = 0 ∨ b = 0) (hd : d = a - b) : d⁺ = a ∧ d⁻ = b := by
  subst hd
  rcases h with rfl | rfl
  · rw [zero_sub]
    refine ⟨posPart_eq_zero.2 (by omega), ?_⟩
    rw [negPart_eq_neg.2 (by omega)]
    omega
  · rw [sub_zero]
    exact ⟨posPart_eq_self.2 ha, negPart_eq_zero.2 ha⟩

/-- The divisor of `θ_a ∘ F` is the divisor of zeros of `f - a`, and the divisor of `θ_∞ ∘ F` is
the divisor of poles of `f`, i.e. of `f - a`. -/
theorem _root_.Meromorphic.sectionDivisor_theta_coe_and_infty (hf : Meromorphic f) {a : ℂ}
    (ha : ∃ z, toRiemannSphere f z ≠ (a : OnePoint ℂ)) :
    sectionDivisor (theta a) (toRiemannSphere f) = (MeromorphicOn.divisor (f · - a) univ)⁺ ∧
    sectionDivisor (theta ∞) (toRiemannSphere f) = (MeromorphicOn.divisor (f · - a) univ)⁻ := by
  have hD := sectionDivisor_sub_sectionDivisor_eq_divisor_sectionRatio
    hf.contMDiff_toRiemannSphere (contMDiff_theta (a : OnePoint ℂ)) (contMDiff_theta ∞)
    (hf.sectionOrderAt_theta_ne_top ha) (hf.sectionOrderAt_theta_ne_top
      hf.exists_toRiemannSphere_ne_infty)
  rw [MeromorphicOn.divisor_congr_codiscreteWithin (hf.sectionRatio_theta_comp_eventuallyEq a)
    isOpen_univ] at hD
  have key : ∀ z, (MeromorphicOn.divisor (f · - a) univ z)⁺
        = sectionDivisor (theta a) (toRiemannSphere f) z
      ∧ (MeromorphicOn.divisor (f · - a) univ z)⁻
        = sectionDivisor (theta ∞) (toRiemannSphere f) z := by
    intro z
    have h₀ : (0 : ℤ) ≤ sectionDivisor (theta a) (toRiemannSphere f) z := by
      simpa using sectionDivisor_nonneg (σ := theta a) (f := toRiemannSphere f) z
    have h₁ : (0 : ℤ) ≤ sectionDivisor (theta ∞) (toRiemannSphere f) z := by
      simpa using sectionDivisor_nonneg (σ := theta ∞) (f := toRiemannSphere f) z
    have hz : sectionDivisor (theta a) (toRiemannSphere f) z = 0
        ∨ sectionDivisor (theta ∞) (toRiemannSphere f) z = 0 := by
      by_cases h : toRiemannSphere f z = (a : OnePoint ℂ)
      · right
        apply sectionDivisor_apply_eq_zero_of_ne_zero
        rw [ne_eq, theta_apply_eq_zero_iff, h]
        exact coe_ne_infty a
      · left
        apply sectionDivisor_apply_eq_zero_of_ne_zero
        rwa [ne_eq, theta_apply_eq_zero_iff]
    have hd : MeromorphicOn.divisor (f · - a) univ z
        = sectionDivisor (theta a) (toRiemannSphere f) z
          - sectionDivisor (theta ∞) (toRiemannSphere f) z := by
      have := congrArg (fun D ↦ D z) hD
      simpa using this.symm
    exact posPart_eq_and_negPart_eq_of_eq_sub h₀ h₁ hz hd
  constructor
  · ext z
    rw [locallyFinsuppWithin.posPart_apply]
    exact (key z).1.symm
  · ext z
    rw [locallyFinsuppWithin.negPart_apply]
    exact (key z).2.symm

/-- The divisor of `θ_a ∘ F` is the divisor of zeros of `f - a`. -/
theorem _root_.Meromorphic.sectionDivisor_theta_coe (hf : Meromorphic f) {a : ℂ}
    (ha : ∃ z, toRiemannSphere f z ≠ (a : OnePoint ℂ)) :
    sectionDivisor (theta a) (toRiemannSphere f) = (MeromorphicOn.divisor (f · - a) univ)⁺ :=
  (hf.sectionDivisor_theta_coe_and_infty ha).1

/-- The divisor of `θ_∞ ∘ F` is the divisor of poles of `f`. -/
theorem _root_.Meromorphic.sectionDivisor_theta_infty (hf : Meromorphic f) :
    sectionDivisor (theta ∞) (toRiemannSphere f) = (MeromorphicOn.divisor f univ)⁻ := by
  by_cases h : ∃ z, toRiemannSphere f z ≠ ((0 : ℂ) : OnePoint ℂ)
  · have := (hf.sectionDivisor_theta_coe_and_infty h).2
    simpa using this
  · -- `f` vanishes identically: both sides are zero
    push Not at h
    have hf0 : f =ᶠ[codiscrete ℂ] 0 := by
      filter_upwards [hf.toRiemannSphere_eventuallyEq_coe] with z hz
      have := h z
      rw [hz, coe_eq_coe] at this
      simpa using this
    rw [MeromorphicOn.divisor_congr_codiscreteWithin hf0 isOpen_univ]
    ext z
    rw [sectionDivisor_apply_eq_zero_of_ne_zero]
    · simp
    · rw [ne_eq, theta_apply_eq_zero_iff, h z]
      exact coe_ne_infty 0

/-!
## Counting functions: exact agreement
-/

/-- The counting function of `θ_∞` along `F` is the classical counting function of the poles of
`f`. -/
theorem _root_.Meromorphic.logCountingSection_theta_infty (hf : Meromorphic f) :
    logCountingSection (toRiemannSphere f) (theta ∞) = logCounting f ⊤ := by
  rw [logCountingSection_def, hf.sectionDivisor_theta_infty, logCounting_top]

/-- The counting function of `θ_a` along `F` is the classical counting function of the
`a`-points of `f`. -/
theorem _root_.Meromorphic.logCountingSection_theta_coe (hf : Meromorphic f) {a : ℂ}
    (ha : ∃ z, toRiemannSphere f z ≠ (a : OnePoint ℂ)) :
    logCountingSection (toRiemannSphere f) (theta a) = logCounting f a := by
  rw [logCountingSection_def, hf.sectionDivisor_theta_coe ha, logCounting_coe]

/-!
## Proximity functions: agreement up to explicit constants
-/

/-- The proximity function of `θ_∞` along `F` differs from the classical proximity function of
`f` at `∞` by at most `log 2 / 2`. -/
theorem _root_.Meromorphic.abs_proximitySection_theta_infty_sub_proximity_le (hf : Meromorphic f)
    {r : ℝ} (hr : r ≠ 0) :
    |proximitySection (toRiemannSphere f) (theta ∞) r - proximity f ⊤ r| ≤ log 2 / 2 := by
  have h₁ : CircleIntegrable (fun z ↦ log ‖theta ∞ (toRiemannSphere f z)‖⁻¹) 0 r :=
    (hf.analyticAlong_theta ∞).circleIntegrable_log_norm_inv r
  have h₂ : CircleIntegrable (log⁺ ‖f ·‖) 0 r :=
    MeromorphicOn.circleIntegrable_posLog_norm hf.meromorphicOn
  -- The difference of the integrands, away from a discrete set
  have hev : (fun z ↦ log ‖theta ∞ (toRiemannSphere f z)‖⁻¹ - log⁺ ‖f z‖)
      =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)] fun z ↦ log (1 + ‖f z‖ ^ 2) / 2 - log⁺ ‖f z‖ := by
    filter_upwards [hf.toRiemannSphere_eventuallyEq_coe.filter_mono
      (codiscreteWithin_mono (subset_univ _))] with z hz
    rw [hz, norm_theta_infty_coe, one_div, _root_.inv_inv, log_sqrt (by positivity)]
  have h₃ : CircleIntegrable (fun z ↦ log (1 + ‖f z‖ ^ 2) / 2 - log⁺ ‖f z‖) 0 r :=
    (h₁.sub h₂).congr_codiscreteWithin hev
  rw [proximitySection, proximity_top, ← circleAverage_fun_sub h₁ h₂,
    circleAverage_congr_codiscreteWithin hev hr, abs_le]
  constructor
  · rw [← circleAverage_const (-(log 2 / 2)) 0 r]
    exact circleAverage_mono (circleIntegrable_const _ _ _) h₃ fun z _ ↦
      (abs_le.1 (abs_log_one_add_sq_div_two_sub_posLog_le (norm_nonneg (f z)))).1
  · exact circleAverage_mono_on_of_le_circle h₃ fun z _ ↦
      (abs_le.1 (abs_log_one_add_sq_div_two_sub_posLog_le (norm_nonneg (f z)))).2

/-- The proximity function of `θ_a` along `F` differs from the classical proximity function of
`f` at `a` by at most `log 2 / 2 + log 2 + log⁺ ‖a‖`. -/
theorem _root_.Meromorphic.abs_proximitySection_theta_coe_sub_proximity_le (hf : Meromorphic f)
    {a : ℂ} (ha : ∃ z, toRiemannSphere f z ≠ (a : OnePoint ℂ)) {r : ℝ} (hr : r ≠ 0) :
    |proximitySection (toRiemannSphere f) (theta a) r - proximity f a r|
      ≤ log 2 / 2 + (log 2 + log⁺ ‖a‖) := by
  have h₁ : CircleIntegrable (fun z ↦ log ‖theta a (toRiemannSphere f z)‖⁻¹) 0 r :=
    (hf.analyticAlong_theta a).circleIntegrable_log_norm_inv r
  have h₂ : CircleIntegrable (log⁺ ‖f · - a‖⁻¹) 0 r := by
    have hm : Meromorphic (fun z ↦ f z - a)⁻¹ := (by fun_prop : Meromorphic (f · - a)).inv
    simpa [Pi.inv_apply, norm_inv] using
      MeromorphicOn.circleIntegrable_posLog_norm (f := (fun z ↦ f z - a)⁻¹) hm.meromorphicOn
  -- The difference of the integrands, away from a discrete set
  have hev : (fun z ↦ log ‖theta a (toRiemannSphere f z)‖⁻¹ - log⁺ ‖f z - a‖⁻¹)
      =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)]
        fun z ↦ log (1 + ‖f z‖ ^ 2) / 2 - log⁺ ‖f z - a‖ := by
    filter_upwards [hf.toRiemannSphere_eventuallyEq_coe.filter_mono
      (codiscreteWithin_mono (subset_univ _)),
      ((hf.analyticAlong_theta a).eventually_ne_zero_codiscrete
        (hf.sectionOrderAt_theta_ne_top ha)).filter_mono
        (codiscreteWithin_mono (subset_univ _))] with z hz hz'
    rw [hz] at hz' ⊢
    have hne : f z - a ≠ 0 := by
      rw [ne_eq, theta_apply_eq_zero_iff, coe_eq_coe] at hz'
      exact sub_ne_zero.2 hz'
    have hne' : ‖f z - a‖ ≠ 0 := norm_ne_zero_iff.2 hne
    rw [norm_theta_coe_coe, inv_div, log_div (by positivity) hne', log_sqrt (by positivity),
      ← posLog_sub_posLog_inv (x := ‖f z - a‖)]
    ring
  have h₃ : CircleIntegrable (fun z ↦ log (1 + ‖f z‖ ^ 2) / 2 - log⁺ ‖f z - a‖) 0 r :=
    (h₁.sub h₂).congr_codiscreteWithin hev
  have hbound : ∀ z, |log (1 + ‖f z‖ ^ 2) / 2 - log⁺ ‖f z - a‖|
      ≤ log 2 / 2 + (log 2 + log⁺ ‖a‖) := fun z ↦ by
      calc |log (1 + ‖f z‖ ^ 2) / 2 - log⁺ ‖f z - a‖|
          = |(log (1 + ‖f z‖ ^ 2) / 2 - log⁺ ‖f z‖) + (log⁺ ‖f z‖ - log⁺ ‖f z - a‖)| := by
            ring_nf
        _ ≤ |log (1 + ‖f z‖ ^ 2) / 2 - log⁺ ‖f z‖| + |log⁺ ‖f z‖ - log⁺ ‖f z - a‖| :=
            abs_add_le _ _
        _ ≤ log 2 / 2 + (log 2 + log⁺ ‖a‖) :=
            add_le_add (abs_log_one_add_sq_div_two_sub_posLog_le (norm_nonneg _))
              (abs_posLog_norm_sub_posLog_norm_sub_le _ _)
  rw [proximitySection, proximity_coe, ← circleAverage_fun_sub h₁ h₂,
    circleAverage_congr_codiscreteWithin hev hr, abs_le]
  constructor
  · rw [← circleAverage_const (-(log 2 / 2 + (log 2 + log⁺ ‖a‖))) 0 r]
    exact circleAverage_mono (circleIntegrable_const _ _ _) h₃ fun z _ ↦ (abs_le.1 (hbound z)).1
  · exact circleAverage_mono_on_of_le_circle h₃ fun z _ ↦ (abs_le.1 (hbound z)).2

/-!
## Characteristic functions: agreement up to explicit constants
-/

/-- The characteristic function of `θ_∞` along `F` differs from the classical characteristic
function of `f` by at most `log 2 / 2`. -/
theorem _root_.Meromorphic.abs_characteristicSection_theta_infty_sub_characteristic_le
    (hf : Meromorphic f) {r : ℝ} (hr : r ≠ 0) :
    |characteristicSection (toRiemannSphere f) (theta ∞) r - characteristic f ⊤ r|
      ≤ log 2 / 2 := by
  have : characteristic f ⊤ r = proximity f ⊤ r + logCounting f ⊤ r := rfl
  rw [this, characteristicSection_def, Pi.add_apply, hf.logCountingSection_theta_infty,
    add_sub_add_right_eq_sub]
  exact hf.abs_proximitySection_theta_infty_sub_proximity_le hr

/-- The characteristic function of `θ_a` along `F` differs from the classical characteristic
function of `f` for the value `a` by at most `log 2 / 2 + log 2 + log⁺ ‖a‖`. -/
theorem _root_.Meromorphic.abs_characteristicSection_theta_coe_sub_characteristic_le
    (hf : Meromorphic f) {a : ℂ} (ha : ∃ z, toRiemannSphere f z ≠ (a : OnePoint ℂ)) {r : ℝ}
    (hr : r ≠ 0) :
    |characteristicSection (toRiemannSphere f) (theta a) r - characteristic f a r|
      ≤ log 2 / 2 + (log 2 + log⁺ ‖a‖) := by
  have : characteristic f a r = proximity f a r + logCounting f a r := rfl
  rw [this, characteristicSection_def, Pi.add_apply, hf.logCountingSection_theta_coe ha,
    add_sub_add_right_eq_sub]
  exact hf.abs_proximitySection_theta_coe_sub_proximity_le ha hr

/-- The characteristic function of `θ_∞` along `F` and the classical characteristic function of
`f` differ by a bounded function. -/
theorem _root_.Meromorphic.isBigO_characteristicSection_theta_infty_sub_characteristic
    (hf : Meromorphic f) :
    (characteristicSection (toRiemannSphere f) (theta ∞) - characteristic f ⊤)
      =O[atTop] (1 : ℝ → ℝ) := by
  apply Asymptotics.IsBigO.of_bound (log 2 / 2)
  filter_upwards [eventually_ne_atTop 0] with r hr
  simpa using hf.abs_characteristicSection_theta_infty_sub_characteristic_le hr

end ValueDistribution
