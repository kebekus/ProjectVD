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
open scoped Real MeasureTheory Metric


namespace ValueDistribution

/-- Specialized version of the Jensen-type identity for `g := f - a`. -/
lemma Cartan.logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top
    {f : ℂ → ℂ} (h : Meromorphic f) {R : ℝ} (hR : R ≠ 0) (a : ℂ) :
    logCounting f a R + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ =
      circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R := by
  have hJ :
      logCounting f a R - logCounting f ⊤ R = circleAverage (log ‖f · - a‖) 0 R
        - log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ := by
    rw [logCounting_coe_eq_logCounting_sub_const_zero, ← logCounting_sub_const h]
    exact logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const (by fun_prop) hR
  linarith

lemma circleAverage_add_const {f : ℂ → ℝ} {c : ℂ} {R : ℝ} {x : ℝ}
    (hf : CircleIntegrable f c R) :
    circleAverage (f · + x) c R = circleAverage f c R + x := by
  exact (circleAverage_add (c := c) (R := R) (f₁ := f) (f₂ := fun _ : ℂ ↦ x) hf
    (circleIntegrable_const x c R)).trans (by rw [circleAverage_const])

/-- Circle integrability of `a ↦ logCounting f a R` follows from the one-variable Cartan identity
once the logarithmic trailing-coefficient term is known to be circle integrable. -/
lemma circleIntegrable_logCounting_of_trailing {f : ℂ → ℂ} (h : Meromorphic f)
    {R : ℝ}
    (htrailing : CircleIntegrable (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1) :
    CircleIntegrable (fun a : ℂ ↦ logCounting f (a : WithTop ℂ) R) 0 1 := by
  by_cases hR_ne : R = 0
  · simp [hR_ne, ValueDistribution.logCounting_eval_zero]
  have hR : R ≠ 0 := hR_ne
  let H1 := fun a ↦ circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R
  let H2 := fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖
  have hH1_int : CircleIntegrable H1 0 1 := by
    exact (circleIntegrable_circleAverage_log_norm_sub h).add
      (circleIntegrable_const (logCounting f ⊤ R) 0 1)
  have h_eq : (fun a : ℂ ↦ logCounting f (a : WithTop ℂ) R) = H1 - H2 := by
    funext a
    have h_id := Cartan.logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top
      h hR a
    simp [H1, H2] at h_id ⊢
    exact eq_sub_of_add_eq h_id
  rw [h_eq]
  exact hH1_int.sub htrailing

/-- For a meromorphic function on `ℂ`, the value-distribution counting function is circle integrable
in the value variable along the unit circle. -/
theorem circleIntegrable_logCounting {f : ℂ → ℂ} (h : Meromorphic f) {R : ℝ} :
    CircleIntegrable (fun a : ℂ ↦ logCounting f (a : WithTop ℂ) R) 0 1 :=
  circleIntegrable_logCounting_of_trailing h
    circleIntegrable_log_trailingCoeff_of_meromorphic

/-- Auxiliary form of Cartan's identity with the trailing-coefficient average left explicit. -/
theorem characteristic_top_eq_circleAverage_logCounting_add_circleAverage_log_trailingCoeff_aux
    {r : ℝ} {f : ℂ → ℂ} (hr : r ≠ 0) (h : Meromorphic f)
    (hci_trailing : CircleIntegrable (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1) :
    characteristic f ⊤ r
      = circleAverage (logCounting f · r) 0 1 + circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  have hci_counting : CircleIntegrable (fun a : ℂ ↦ logCounting f (a : WithTop ℂ) r) 0 1 :=
    circleIntegrable_logCounting_of_trailing h (R := r) hci_trailing
  have hci_inner : CircleIntegrable (fun a ↦ circleAverage (log ‖f · - a‖) 0 r) 0 1 :=
    circleIntegrable_circleAverage_log_norm_sub h
  calc characteristic f ⊤ r
    _ = circleAverage (log⁺ ‖f ·‖) 0 r + logCounting f ⊤ r := by
      simp [ValueDistribution.characteristic, ValueDistribution.proximity]
    _ = circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 r) 0 1 + logCounting f ⊤ r := by
      rw [← proximity_top, ← proximity_top_eq_circleAverage_circleAverage h]
    _ = circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 r + logCounting f ⊤ r) 0 1 := by
      rw [← circleAverage_add_const hci_inner]
    _ = circleAverage (fun a : ℂ ↦ logCounting f (a : WithTop ℂ) r
          + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
      apply circleAverage_congr_sphere
      intro a ha
      simp [Cartan.logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top h hr a]
    _ = circleAverage (logCounting f · r) 0 1
          + circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
      exact circleAverage_add
          (c := 0) (R := 1)
          (f₁ := fun a : ℂ ↦ logCounting f (a : WithTop ℂ) r)
          (f₂ := fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖)
          hci_counting hci_trailing

/-- Cartan's formula with the additive constant written explicitly as a circle average of the
logarithm of the first nonzero Laurent coefficient of `f - a` at the origin. -/
theorem characteristic_top_eq_circleAverage_logCounting_add_circleAverage_log_trailingCoeff
    {r : ℝ} {f : ℂ → ℂ} (hr : r ≠ 0) (h : Meromorphic f) :
    characteristic f ⊤ r =
      circleAverage (logCounting f · r) 0 1
        + circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  exact characteristic_top_eq_circleAverage_logCounting_add_circleAverage_log_trailingCoeff_aux
    hr h circleIntegrable_log_trailingCoeff_of_meromorphic

/-- Cartan's formula in the zero case `0 < meromorphicOrderAt f 0`. -/
theorem characteristic_top_eq_circleAverage_logCounting_of_meromorphicOrderAt_pos
    {r : ℝ} {f : ℂ → ℂ} (hr : r ≠ 0) (h : Meromorphic f)
    (h₂ : 0 < meromorphicOrderAt f 0) :
    characteristic f ⊤ r = circleAverage (logCounting f · r) 0 1 := by
  calc characteristic f ⊤ r
    _ = circleAverage (logCounting f · r) 0 1
          + circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 :=
      characteristic_top_eq_circleAverage_logCounting_add_circleAverage_log_trailingCoeff hr h
    _ = circleAverage (logCounting f · r) 0 1 := by
      simp [circleAverage_log_norm_trailingCoeff_of_pos_meromorphicOrderAt h₂]

/-- Qualitative Cartan formula: away from `0`, the difference between `characteristic f ⊤` and
`circleAverage (logCounting f · ·) 0 1` is constant. -/
theorem characteristic_top_eq_circleAverage_logCounting_add_const {f : ℂ → ℂ} (h : Meromorphic f) :
    ∃ const, ∀ r ≠ 0, characteristic f ⊤ r = circleAverage (logCounting f · r) 0 1 + const := by
  refine ⟨circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1, ?_⟩
  intro r hr
  exact characteristic_top_eq_circleAverage_logCounting_add_circleAverage_log_trailingCoeff
      (r := r) hr h

end ValueDistribution
