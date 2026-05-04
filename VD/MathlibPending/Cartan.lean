/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Stefan Kebekus
-/

module

public import VD.MathlibSubmitted.Cartan
public import VD.MathlibSubmitted.ProximityIntegral
public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem

public section

open Real

namespace ValueDistribution

theorem CircleIntegrable.sub {E : Type*} [NormedAddCommGroup E] {f g : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    CircleIntegrable (f - g) c R :=
  hf.sub hg

variable
  {f : ℂ → ℂ} {R : ℝ}

/- Specialized Jensen-type identity -/
private lemma logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top
    (h : Meromorphic f) (hR : R ≠ 0) (a : ℂ) :
    logCounting f a R + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ =
      circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R := by
  have : logCounting f a R - logCounting f ⊤ R = circleAverage (log ‖f · - a‖) 0 R
        - log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ := by
    rw [logCounting_coe_eq_logCounting_sub_const_zero, ← logCounting_sub_const h]
    exact logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const (by fun_prop) hR
  linarith

/--
Circle integrability of the term `logCounting f · R` that appears in Cartan's
formula.
-/
theorem circleIntegrable_logCounting (h : Meromorphic f) :
    CircleIntegrable (logCounting f · R) 0 1 := by
  by_cases hR : R = 0
  · simp [hR, ValueDistribution.logCounting_eval_zero]
  let H1 := fun a ↦ circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R
  let H2 := fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖
  have : (fun a : ℂ ↦ logCounting f a R) = H1 - H2 := by
    ext a
    simpa [Pi.sub_apply, H1, H2] using eq_sub_of_add_eq
      (logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top h hR a)
  rw [this]
  exact CircleIntegrable.sub ((circleIntegrable_circleAverage_log_norm_sub h).add
      (circleIntegrable_const (logCounting f ⊤ R) 0 1))
    circleIntegrable_log_trailingCoeff_of_meromorphic

/-!
## Cartan's formula
-/

/--
**Cartan's formula** with the additive constant written explicitly as a circle
average of the logarithm of the first nonzero Laurent coefficient of `f - a` at
the origin.

See `circleIntegrable_logCounting` and
`circleIntegrable_log_trailingCoeff_of_meromorphic` for the facts that the
summands are acutally circle integrable.
-/
theorem characteristic_top_eq_circleAverage_add_circleAverage (h : Meromorphic f) (hR : R ≠ 0) :
    characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1
      + circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  calc characteristic f ⊤ R
    _ = circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R) 0 1 := by
      simp only [characteristic, proximity, ↓reduceDIte, Pi.add_apply]
      rw [← proximity_top, ← proximity_top_eq_circleAverage_circleAverage h,
        circleAverage_fun_add (circleIntegrable_circleAverage_log_norm_sub h)
          (circleIntegrable_const (logCounting f ⊤ R) 0 1), circleAverage_const]
    _ = circleAverage (logCounting f · R) 0 1
          + circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
      rw [← circleAverage_add (circleIntegrable_logCounting h)
        circleIntegrable_log_trailingCoeff_of_meromorphic, circleAverage_congr_sphere]
      intro a ha
      simp [logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top h hR a]

/--
**Cartan's formula** in case where `0 < meromorphicOrderAt f 0`.
-/
theorem characteristic_top_eq_circleAverage_of_meromorphicOrderAt_pos
    (h₁f : Meromorphic f) (h₂f : 0 < meromorphicOrderAt f 0) (hR : R ≠ 0) :
    characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1 := by
  rw [characteristic_top_eq_circleAverage_add_circleAverage h₁f hR]
  simp [circleAverage_log_norm_trailingCoeff_of_pos_meromorphicOrderAt h₂f]

/--
Qualitative version of **Cartan's formula**: Away from `0`, the difference
between `characteristic f ⊤` and `circleAverage (logCounting f · ·) 0 1` is
constant.
-/
theorem characteristic_top_eq_circleAverage_add_const (h : Meromorphic f) :
    ∃ const, ∀ R ≠ 0, characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1 + const :=
  ⟨circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1,
    fun _ hr ↦ characteristic_top_eq_circleAverage_add_circleAverage h hr⟩

/-!
## Application: Monotonicity of the Characteristic Function
-/

/--
The characteristic function is monotone on `(0, ∞)`.

This result is surprisingly non-trivial, given that the proximity function is
not monotone in general.
-/
theorem characteristic_monotoneOn (h : Meromorphic f) :
    MonotoneOn (characteristic f ⊤) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [characteristic_top_eq_circleAverage_add_circleAverage h ha.ne',
    characteristic_top_eq_circleAverage_add_circleAverage h hb.ne']
  gcongr
  <;> try exact circleIntegrable_logCounting h
  exact logCounting_monotoneOn ha hb hab

end ValueDistribution
