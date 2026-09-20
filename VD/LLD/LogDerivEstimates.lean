/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.MeanInequalitiesPow
import VD.LLD.CircleAverageEstimates
import VD.MathlibSubmitted.JensenInequality

/-!
# Estimates for the Two-Radius Bound — LLD work package C4, general part

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §5.

This file collects the general-interest lemmas on which the two-radius estimate for the Lemma on
the Logarithmic Derivative (`VD/LLD/LogDerivTwoRadius.lean`) rests. None of them mentions
`logDeriv`. They are grouped by Mathlib target file.

## Main results

- `NNReal.rpow_sum_le_sum_rpow`, `Real.rpow_sum_le_sum_rpow`: for `0 < p ≤ 1`, the function
  `x ↦ x ^ p` is subadditive on finite sums of nonnegative reals.
- `CircleIntegrable.norm`, `circleAverage_mono_codiscreteWithin`: circle averages respect
  inequalities that hold away from a discrete subset of the circle.
- `ValueDistribution.proximity_add_proximity_inv_eq_circleAverage`: `m(r, f) + m(r, 1/f)` is the
  circle average of `|log ‖f‖|`, the companion of `proximity_sub_proximity_inv_eq_circleAverage`.
- `ValueDistribution.proximity_le_characteristic`,
  `ValueDistribution.logCounting_le_characteristic`: both summands of the characteristic function
  are bounded by it.
- `ValueDistribution.finsum_abs_divisor_ball_mul_log_le`: the zeros and poles of `f` in a ball,
  counted with multiplicity and weighted by `log (R / ρ)`, are bounded by `N(R, 0) + N(R, ∞)`.
- `circleAverage_posLog_norm_le_of_le_add_sum_inv_norm_sub`, the **exponent-`1/2` trick**: if
  `‖F‖` is bounded on a circle by a constant plus a finite sum of simple poles `m a / ‖· - a‖`,
  then the circle average of `log⁺ ‖F‖` depends only logarithmically on the total weight
  `∑ a ∈ s, m a`.

## Upstreaming notes

- `NNReal.rpow_sum_le_sum_rpow`, `Real.rpow_sum_le_sum_rpow` →
  `Mathlib/Analysis/MeanInequalitiesPow.lean`, after `NNReal.rpow_add_le_add_rpow` and
  `Real.rpow_add_le_add_rpow`.
- `CircleIntegrable.norm` → `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`, next to
  `CircleIntegrable.abs`.
- `circleAverage_mono_codiscreteWithin` → `Mathlib/MeasureTheory/Integral/CircleAverage.lean`,
  next to `circleAverage_congr_codiscreteWithin`.
- `proximity_add_proximity_inv_eq_circleAverage` →
  `Mathlib/Analysis/Complex/ValueDistribution/Proximity/Basic.lean`, next to
  `proximity_sub_proximity_inv_eq_circleAverage`.
- `proximity_le_characteristic`, `logCounting_le_characteristic` →
  `Mathlib/Analysis/Complex/ValueDistribution/CharacteristicFunction.lean`, next to
  `characteristic_nonneg`.
- `finsum_abs_divisor_ball_mul_log_le` →
  `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean`, after
  `sum_toClosedBall_le_logCounting`.
- `circleAverage_posLog_norm_le_of_le_add_sum_inv_norm_sub` → the file of the Lemma on the
  Logarithmic Derivative, `Mathlib/Analysis/Complex/ValueDistribution/LogDerivLemma.lean`.

The private lemma `circleIntegrable_posLog_comp` duplicates a private lemma of
`VD/MathlibSubmitted/JensenInequality.lean` (C1, in review); expose it there once that PR is merged.
-/

open Complex Filter Function MeasureTheory MeromorphicOn Metric Real Set Topology

/-!
## Subadditivity of Real Powers
-/

open scoped NNReal in
/-- For `0 < p ≤ 1`, the function `x ↦ x ^ p` is subadditive on finite sums in `ℝ≥0`. The binary
case is `NNReal.rpow_add_le_add_rpow`. The hypothesis `0 < p` cannot be weakened to `0 ≤ p` as in
the binary case: for `p = 0` and `s = ∅` the left side is `1`. -/
theorem NNReal.rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, f i) ^ p ≤ ∑ i ∈ s, f i ^ p := by
  induction s using Finset.cons_induction with
  | empty => simp [NNReal.zero_rpow hp.ne']
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    calc (f a + ∑ i ∈ s, f i) ^ p
        ≤ f a ^ p + (∑ i ∈ s, f i) ^ p := NNReal.rpow_add_le_add_rpow _ _ hp.le hp1
      _ ≤ f a ^ p + ∑ i ∈ s, f i ^ p := by gcongr

/-- For `0 < p ≤ 1`, the function `x ↦ x ^ p` is subadditive on finite sums of nonnegative reals.
The binary case is `Real.rpow_add_le_add_rpow`; see `NNReal.rpow_sum_le_sum_rpow` for the
hypothesis `0 < p`. -/
theorem Real.rpow_sum_le_sum_rpow {ι : Type*} {s : Finset ι} {f : ι → ℝ} {p : ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, f i) ^ p ≤ ∑ i ∈ s, f i ^ p := by
  calc (∑ i ∈ s, f i) ^ p
      = (∑ i ∈ s, ((f i).toNNReal : ℝ)) ^ p := by
        rw [Finset.sum_congr rfl fun i hi ↦ (Real.coe_toNNReal _ (hf i hi)).symm]
    _ ≤ ∑ i ∈ s, ((f i).toNNReal : ℝ) ^ p := by
        exact_mod_cast NNReal.rpow_sum_le_sum_rpow s (fun i ↦ (f i).toNNReal) hp hp1
    _ = ∑ i ∈ s, f i ^ p := Finset.sum_congr rfl fun i hi ↦ by rw [Real.coe_toNNReal _ (hf i hi)]

/-!
## Circle Averages
-/

/-- If `f` is circle integrable, then so is `‖f ·‖`. Analogue of `IntervalIntegrable.norm`. -/
@[fun_prop]
theorem CircleIntegrable.norm {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    CircleIntegrable (‖f ·‖) c R :=
  IntervalIntegrable.norm hf

/-- Circle averages respect inequalities that hold away from a discrete subset of the circle.
Compare `circleAverage_mono`, which requires the inequality everywhere on the circle. -/
theorem circleAverage_mono_codiscreteWithin {f₁ f₂ : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : R ≠ 0)
    (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R)
    (h : f₁ ≤ᶠ[codiscreteWithin (sphere c |R|)] f₂) :
    circleAverage f₁ c R ≤ circleAverage f₂ c R := by
  rw [circleAverage_def, circleAverage_def, smul_eq_mul, smul_eq_mul]
  gcongr
  exact intervalIntegral.integral_mono_ae_restrict (by positivity) hf₁ hf₂
    (ae_restrict_le_codiscreteWithin measurableSet_Icc
      (codiscreteWithin_mono (subset_univ _) (circleMap_preimage_codiscrete hR h)))

-- Duplicate of a private lemma in `VD/MathlibSubmitted/JensenInequality.lean`; expose it there
-- once that PR is merged.
private lemma circleIntegrable_posLog_comp {u : ℂ → ℝ} {r : ℝ} (hu : CircleIntegrable u 0 r) :
    CircleIntegrable (fun w ↦ log⁺ (u w)) 0 r := by
  refine IntervalIntegrable.mono_fun hu.abs ?_ ?_
  · exact continuous_posLog.comp_aestronglyMeasurable
      (intervalIntegrable_iff.1 hu).aestronglyMeasurable
  · filter_upwards with θ
    simpa [abs_of_nonneg posLog_nonneg] using posLog_le_abs _

/-!
## Value Distribution: Elementary Comparisons
-/

namespace ValueDistribution

/-- The sum of the proximity functions of `f` and `f⁻¹` for the value `⊤` is the circle average of
`|log ‖f ·‖|`. Companion of `proximity_sub_proximity_inv_eq_circleAverage`. -/
theorem proximity_add_proximity_inv_eq_circleAverage {f : ℂ → ℂ} (hf : Meromorphic f) :
    proximity f ⊤ + proximity f⁻¹ ⊤ = circleAverage (|Real.log ‖f ·‖|) 0 := by
  ext R
  rw [Pi.add_apply, proximity_top, proximity_top, ← circleAverage_add
    hf.meromorphicOn.circleIntegrable_posLog_norm hf.inv.meromorphicOn.circleIntegrable_posLog_norm]
  simp [Pi.add_def, abs_log_eq_posLog_add_posLog_inv]

/-- For `1 ≤ r`, the proximity function is bounded by the characteristic function. -/
theorem proximity_le_characteristic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a : WithTop E} {r : ℝ} (hr : 1 ≤ r) :
    proximity f a r ≤ characteristic f a r :=
  le_add_of_nonneg_right (logCounting_nonneg hr)

/-- The logarithmic counting function is bounded by the characteristic function. -/
theorem logCounting_le_characteristic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a : WithTop E} {r : ℝ} :
    logCounting f a r ≤ characteristic f a r :=
  le_add_of_nonneg_left (proximity_nonneg r)

/-!
## Counting Zeros and Poles in a Ball
-/

/-- The zeros and poles of a meromorphic function `f` in `ball 0 ρ`, counted with multiplicity and
weighted by `log (R / ρ)`, are bounded by the logarithmic counting functions of `f` for the values
`0` and `⊤` at any larger radius `R`. This is
`Function.locallyFinsuppWithin.sum_toClosedBall_le_logCounting`, applied to the divisor `D⁺ + D⁻`,
where `D` is the divisor of `f` on the plane. -/
theorem finsum_abs_divisor_ball_mul_log_le {f : ℂ → ℂ} {ρ R : ℝ} (hf : Meromorphic f)
    (hρ : 1 ≤ ρ) (hρR : ρ < R) :
    (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) * Real.log (R / ρ)
      ≤ logCounting f 0 R + logCounting f ⊤ R := by
  -- The comparison divisor: positive plus negative part of the divisor of `f` on the plane
  set E := (divisor f univ)⁺ + (divisor f univ)⁻ with hE_def
  have hE₀ : 0 ≤ E := add_nonneg (posPart_nonneg _) (negPart_nonneg _)
  -- Term-wise comparison: `|divisor f (ball 0 ρ) a| ≤ E.toClosedBall ρ a`
  have key : ∀ a : ℂ, (|divisor f (ball 0 ρ) a| : ℝ) ≤ (E.toClosedBall ρ a : ℝ) := by
    intro a
    have hEa : E a = |divisor f univ a| := by
      rw [hE_def, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
        Function.locallyFinsuppWithin.posPart_apply, Function.locallyFinsuppWithin.negPart_apply,
        posPart_add_negPart]
    rw [← hf.meromorphicOn.divisor_restrict (subset_univ _),
      Function.locallyFinsuppWithin.toClosedBall_apply,
      Function.locallyFinsuppWithin.restrict_apply, Function.locallyFinsuppWithin.restrict_apply]
    split_ifs with h₁ h₂
    · rw [hEa, Int.cast_abs]
    · exact absurd
        (ball_subset_closedBall.trans (closedBall_subset_closedBall (le_abs_self ρ)) h₁) h₂
    · simpa using Function.locallyFinsuppWithin.le_def.1 hE₀ a
    · simp
  -- Compare the two finite sums
  have hsum : (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) ≤ ∑ᶠ z, (E.toClosedBall ρ z : ℝ) := by
    have hd_fin : (divisor f (ball 0 ρ)).support.Finite :=
      hf.meromorphicOn.divisor_ball_support_finite
    refine finsum_le_finsum ?_ ?_ key
    · refine hd_fin.subset fun a ha ↦ ?_
      simpa only [mem_support, ne_eq, abs_eq_zero, Int.cast_eq_zero] using ha
    · refine (Function.locallyFinsuppWithin.finiteSupport (E.toClosedBall ρ)
        (isCompact_closedBall 0 |ρ|)).subset fun a ha ↦ ?_
      simpa only [mem_support, ne_eq, Int.cast_eq_zero] using ha
  -- The counting function of `E` splits as `N(R, 0) + N(R, ∞)`
  have hsplit : Function.locallyFinsuppWithin.logCounting E R
      = logCounting f 0 R + logCounting f ⊤ R := by
    rw [hE_def, map_add, logCounting_zero, logCounting_top]
    rfl
  have hlog₀ : 0 ≤ Real.log (R / ρ) := Real.log_nonneg ((one_le_div₀ (by linarith)).2 hρR.le)
  calc (∑ᶠ a, (|divisor f (ball 0 ρ) a| : ℝ)) * Real.log (R / ρ)
      ≤ (∑ᶠ z, (E.toClosedBall ρ z : ℝ)) * Real.log (R / ρ) :=
        mul_le_mul_of_nonneg_right hsum hlog₀
    _ ≤ Function.locallyFinsuppWithin.logCounting E R :=
        Function.locallyFinsuppWithin.sum_toClosedBall_le_logCounting hE₀ hρ hρR
    _ = logCounting f 0 R + logCounting f ⊤ R := hsplit

end ValueDistribution

/-!
## The Exponent-`1/2` Trick
-/

/-- **The exponent-`1/2` trick.** Let `F` be a function whose norm is bounded, away from a discrete
subset of the circle `|w| = r`, by a constant `K` plus a finite sum of simple poles
`m a * ‖w - a‖⁻¹` with weights `m a ≥ 1`. Then the circle average of `log⁺ ‖F‖` is bounded by
`log⁺ K` plus twice `log⁺` of the *total weight* `∑ a ∈ s, m a`, up to an absolute constant.

The point is the logarithmic dependence on the total weight: bounding `log⁺` of the sum termwise
(`Real.posLog_sum`) would yield a bound linear in `∑ a ∈ s, m a`. Instead, take square roots
first: `‖F w‖ ^ (1/2)` is bounded by `K ^ (1/2) + ∑ a ∈ s, m a * ‖w - a‖ ^ (-1/2)`, whose circle
average is bounded *uniformly* in the poles `a` (`circleAverage_norm_sub_const_rpow_le`), and
Jensen's inequality `Real.circleAverage_posLog_le_posLog_circleAverage` turns the average of
`log⁺` of this bound into `log⁺` of its average.

The constant `8 * log 2` is `2 * (log 2 + log 2 + log 4)`: one `log 2` from Jensen's inequality,
one from `Real.posLog_add`, and `log 4` from the constant `4 = 2 / (p + 1)` in
`circleAverage_norm_sub_const_rpow_le` at `p = -1/2`; the factor `2` undoes the square root. The
term `log⁺ r⁻¹` is the radius dependence of that same bound; it vanishes for `1 ≤ r`. -/
theorem circleAverage_posLog_norm_le_of_le_add_sum_inv_norm_sub {E : Type*}
    [NormedAddCommGroup E] {F : ℂ → E} {s : Finset ℂ} {m : ℂ → ℝ} {K r : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hm : ∀ a ∈ s, 1 ≤ m a)
    (hF : CircleIntegrable (fun w ↦ log⁺ ‖F w‖) 0 r)
    (h : ∀ᶠ w in codiscreteWithin (sphere (0 : ℂ) r), ‖F w‖ ≤ K + ∑ a ∈ s, m a * ‖w - a‖⁻¹) :
    circleAverage (fun w ↦ log⁺ ‖F w‖) 0 r
      ≤ log⁺ K + 2 * log⁺ (∑ a ∈ s, m a) + log⁺ r⁻¹ + 8 * Real.log 2 := by
  have hm₀ : ∀ a ∈ s, 0 ≤ m a := fun a ha ↦ zero_le_one.trans (hm a ha)
  -- The explicit bound function for `‖F ·‖ ^ (1/2)`
  set g : ℂ → ℝ := (fun _ ↦ K ^ (2⁻¹ : ℝ)) + ∑ a ∈ s, m a • (‖· - a‖ ^ (-(2 : ℝ)⁻¹)) with hg_def
  have hg_apply : ∀ w, g w = K ^ (2⁻¹ : ℝ) + ∑ a ∈ s, m a * ‖w - a‖ ^ (-(2 : ℝ)⁻¹) := fun w ↦ by
    simp only [hg_def, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hg₀ : ∀ w, 0 ≤ g w := fun w ↦ by
    rw [hg_apply]
    exact add_nonneg (rpow_nonneg hK _)
      (Finset.sum_nonneg fun a ha ↦ mul_nonneg (hm₀ a ha) (rpow_nonneg (norm_nonneg _) _))
  -- Step 1: `‖F w‖ ^ (1/2) ≤ g w` away from a discrete set, by subadditivity of `x ↦ x ^ (1/2)`
  have step1 : ∀ᶠ w in codiscreteWithin (sphere (0 : ℂ) r), ‖F w‖ ^ (2⁻¹ : ℝ) ≤ g w := by
    filter_upwards [h] with w hw
    rw [hg_apply]
    have hterm : ∀ a ∈ s, 0 ≤ m a * ‖w - a‖⁻¹ :=
      fun a ha ↦ mul_nonneg (hm₀ a ha) (inv_nonneg.2 (norm_nonneg _))
    calc ‖F w‖ ^ (2⁻¹ : ℝ)
        ≤ (K + ∑ a ∈ s, m a * ‖w - a‖⁻¹) ^ (2⁻¹ : ℝ) :=
          rpow_le_rpow (norm_nonneg _) hw (by norm_num)
      _ ≤ K ^ (2⁻¹ : ℝ) + (∑ a ∈ s, m a * ‖w - a‖⁻¹) ^ (2⁻¹ : ℝ) :=
          Real.rpow_add_le_add_rpow hK (Finset.sum_nonneg hterm) (by norm_num) (by norm_num)
      _ ≤ K ^ (2⁻¹ : ℝ) + ∑ a ∈ s, (m a * ‖w - a‖⁻¹) ^ (2⁻¹ : ℝ) := by
          gcongr
          exact Real.rpow_sum_le_sum_rpow hterm (by norm_num) (by norm_num)
      _ ≤ K ^ (2⁻¹ : ℝ) + ∑ a ∈ s, m a * ‖w - a‖ ^ (-(2 : ℝ)⁻¹) := by
          gcongr with a ha
          rw [mul_rpow (hm₀ a ha) (inv_nonneg.2 (norm_nonneg _)), inv_rpow (norm_nonneg _),
            ← rpow_neg (norm_nonneg _)]
          gcongr
          exact rpow_le_self_of_one_le (hm a ha) (by norm_num)
  -- Step 2: `log⁺ ‖F w‖ = 2 * log⁺ (‖F w‖ ^ (1/2)) ≤ 2 * log⁺ (g w)`
  have step2 : ∀ᶠ w in codiscreteWithin (sphere (0 : ℂ) r), log⁺ ‖F w‖ ≤ 2 * log⁺ (g w) := by
    filter_upwards [step1] with w hw
    have h₁ : log⁺ (‖F w‖ ^ (2⁻¹ : ℝ)) = 2⁻¹ * log⁺ ‖F w‖ :=
      posLog_rpow (neg_one_lt_zero.le.trans (norm_nonneg _)) (by norm_num)
    have h₂ := posLog_le_posLog (neg_one_lt_zero.le.trans (rpow_nonneg (norm_nonneg _) _)) hw
    linarith
  -- Integrability of the bound function and of `log⁺ ∘ g`
  have int_terms : ∀ a ∈ s, CircleIntegrable (m a • (‖· - a‖ ^ (-(2 : ℝ)⁻¹))) 0 r :=
    fun a _ ↦ (circleIntegrable_norm_sub_const_rpow (by norm_num) r).const_smul
  have int_g : CircleIntegrable g 0 r := by
    rw [hg_def]
    exact (circleIntegrable_const _ _ _).add (CircleIntegrable.sum _ int_terms)
  have int_posLog_g : CircleIntegrable (fun w ↦ log⁺ (g w)) 0 r :=
    circleIntegrable_posLog_comp int_g
  -- Step 3: integrate the pointwise bound
  have step3 : circleAverage (fun w ↦ log⁺ ‖F w‖) 0 r
      ≤ 2 * circleAverage (fun w ↦ log⁺ (g w)) 0 r := by
    calc circleAverage (fun w ↦ log⁺ ‖F w‖) 0 r
        ≤ circleAverage (fun w ↦ 2 * log⁺ (g w)) 0 r :=
          circleAverage_mono_codiscreteWithin hr.ne' hF (by fun_prop) (by rwa [abs_of_pos hr])
      _ = 2 * circleAverage (fun w ↦ log⁺ (g w)) 0 r := circleAverage_fun_smul (a := (2 : ℝ))
  -- Step 4: the circle average of `g`, using the uniform bound for the singular terms
  have step4 : circleAverage g 0 r ≤ K ^ (2⁻¹ : ℝ) + 4 * (∑ a ∈ s, m a) * r ^ (-(2 : ℝ)⁻¹) := by
    rw [hg_def, circleAverage_add (circleIntegrable_const _ _ _) (CircleIntegrable.sum _ int_terms),
      circleAverage_const, circleAverage_sum int_terms]
    gcongr
    calc ∑ a ∈ s, circleAverage (m a • (‖· - a‖ ^ (-(2 : ℝ)⁻¹))) 0 r
        = ∑ a ∈ s, m a * circleAverage (‖· - a‖ ^ (-(2 : ℝ)⁻¹)) 0 r := by
          simp only [circleAverage_smul, smul_eq_mul]
      _ ≤ ∑ a ∈ s, m a * (4 * r ^ (-(2 : ℝ)⁻¹)) := by
          gcongr with a ha
          · exact hm₀ a ha
          · have := circleAverage_norm_sub_const_rpow_le (a := a) (c := 0) hr.ne'
              (p := -(2 : ℝ)⁻¹) (by norm_num) (by norm_num)
            rwa [abs_of_pos hr, show 2 / (-(2 : ℝ)⁻¹ + 1) = 4 by norm_num] at this
      _ = 4 * (∑ a ∈ s, m a) * r ^ (-(2 : ℝ)⁻¹) := by rw [← Finset.sum_mul]; ring
  -- Step 5: Jensen's inequality, and expansion of `log⁺` of the resulting bound
  have hC1 : circleAverage (fun w ↦ log⁺ (g w)) 0 r ≤ log⁺ (circleAverage g 0 r) + Real.log 2 :=
    Real.circleAverage_posLog_le_posLog_circleAverage (fun z _ ↦ hg₀ z) int_g
  have hmono : log⁺ (circleAverage g 0 r)
      ≤ log⁺ (K ^ (2⁻¹ : ℝ) + 4 * (∑ a ∈ s, m a) * r ^ (-(2 : ℝ)⁻¹)) :=
    posLog_le_posLog (neg_one_lt_zero.le.trans (circleAverage_nonneg_of_nonneg fun z _ ↦ hg₀ z))
      step4
  have e₁ : log⁺ (K ^ (2⁻¹ : ℝ)) = 2⁻¹ * log⁺ K :=
    posLog_rpow (neg_one_lt_zero.le.trans hK) (by norm_num)
  have e₂ : log⁺ (r ^ (-(2 : ℝ)⁻¹)) = 2⁻¹ * log⁺ r⁻¹ := by
    rw [rpow_neg hr.le, ← inv_rpow hr.le,
      posLog_rpow (neg_one_lt_zero.le.trans (inv_nonneg.2 hr.le)) (by norm_num)]
  have e₃ : log⁺ (4 * (∑ a ∈ s, m a) * r ^ (-(2 : ℝ)⁻¹))
      ≤ 2 * Real.log 2 + log⁺ (∑ a ∈ s, m a) + 2⁻¹ * log⁺ r⁻¹ := by
    have h₄ := posLog_nat_mul (n := 4) (x := ∑ a ∈ s, m a)
    push_cast at h₄
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    calc log⁺ (4 * (∑ a ∈ s, m a) * r ^ (-(2 : ℝ)⁻¹))
        ≤ log⁺ (4 * ∑ a ∈ s, m a) + log⁺ (r ^ (-(2 : ℝ)⁻¹)) := posLog_mul
      _ ≤ 2 * Real.log 2 + log⁺ (∑ a ∈ s, m a) + 2⁻¹ * log⁺ r⁻¹ := by
          rw [e₂]
          linarith
  have e₄ : log⁺ (K ^ (2⁻¹ : ℝ) + 4 * (∑ a ∈ s, m a) * r ^ (-(2 : ℝ)⁻¹))
      ≤ Real.log 2 + log⁺ (K ^ (2⁻¹ : ℝ)) + log⁺ (4 * (∑ a ∈ s, m a) * r ^ (-(2 : ℝ)⁻¹)) :=
    posLog_add
  rw [e₁] at e₄
  linarith
