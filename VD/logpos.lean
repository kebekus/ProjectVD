/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Positive Part of the Logarithm

This file defines the function `log⁺ = r ↦ max 0 (log r)`, and establishes
standard estimates.
-/

open Real


/-!
## Definition, Notation and Reformulations
-/
noncomputable def Real.logpos : ℝ → ℝ := fun r ↦ max 0 (log r)

notation "log⁺" => logpos

theorem Real.logpos_def {r : ℝ} : log⁺ r = max 0 (log r) := rfl

theorem Real.log_eq_logpos_sub_logpos_inv {r : ℝ} : log r = log⁺ r - log⁺ r⁻¹ := by
  rw [logpos_def, logpos_def, log_inv]
  by_cases h : 0 ≤ log r
  · simp [h]
  · rw [not_le] at h
    simp [h, neg_nonneg.mp (Left.nonneg_neg_iff.2 h.le)]

theorem Real.logpos_eq_half_mul_log_add_log_abs {r : ℝ} : log⁺ r = 2⁻¹ * (log r + |log r|) := by
  by_cases hr : 0 ≤ log r
  · simp [logpos, hr, abs_of_nonneg hr]
    ring
  · simp [logpos, le_of_not_ge hr, abs_of_nonpos (le_of_not_ge hr)]


/-!
## Elementary Properties
-/
theorem Real.logpos_nonneg {x : ℝ} : 0 ≤ log⁺ x := by simp [logpos]

theorem Real.logpos_neg (x : ℝ) : log⁺ x = log⁺ (-x) := by simp [logpos]

theorem Real.logpos_abs (x : ℝ) : log⁺ |x| = log⁺ x := by simp [logpos]

theorem Real.logpos_eq_zero_iff (x : ℝ) : log⁺ x = 0 ↔ |x| ≤ 1 := by
  rw [← logpos_abs, ← log_nonpos_iff (abs_nonneg x)]
  simp [logpos]

theorem Real.logpos_eq_log {x : ℝ} (hx : 1 ≤ |x|) : log⁺ x = log x := by
  simp [logpos]
  rw [← log_abs]
  apply log_nonneg hx

theorem Real.logpos_eq_log_of_nat {n : ℕ} : log n = log⁺ n := by
  by_cases hn : n = 0
  · simp [hn, logpos]
  · simp [logpos_eq_log, abs_of_nonneg, Nat.one_le_iff_ne_zero.mpr hn, Nat.cast_nonneg']

theorem Real.monotoneOn_logpos : MonotoneOn log⁺ (Set.Ici 0) := by
  intro x hx y hy hxy
  simp [logpos]
  by_cases h : log x ≤ 0
  · tauto
  · right
    have := log_le_log (lt_trans Real.zero_lt_one ((log_pos_iff hx).1 (not_le.1 h))) hxy
    simp [this]
    linarith

/-!
## Estimates for Sums and Products
-/
theorem Real.logpos_mul {a b : ℝ} :
    log⁺ (a * b) ≤ log⁺ a + log⁺ b := by
  by_cases ha : a = 0
  · simp [ha, logpos]
  by_cases hb : b = 0
  · simp [hb, logpos]
  unfold logpos
  nth_rw 1 [← add_zero 0, log_mul ha hb]
  exact max_add_add_le_max_add_max

theorem Real.logpos_mul_nat {n : ℕ} {a : ℝ} :
    log⁺ (n * a) ≤ log n + log⁺ a := by
  rw [logpos_eq_log_of_nat]
  exact logpos_mul

theorem Real.logpos_sum'' {α : Type} [Fintype α] (f : α → ℝ) :
    log⁺ (∑ t, f t) ≤ log (Fintype.card α) + ∑ t, log⁺ (f t) := by
  -- Trivial case: empty sum
  by_cases hs : (Fintype.card α) = 0
  · simp [hs, Fin.isEmpty', logpos, Fintype.card_eq_zero_iff.mp hs]
  -- Nontrivial case:
  -- Obtain maximal element…
  have nonEmpty : Nonempty α := by
    apply Fintype.card_pos_iff.mp
    exact Nat.zero_lt_of_ne_zero hs
  obtain ⟨t_max, ht_max⟩ := Finite.exists_max (fun t ↦ |f t|)
  -- …then calculate
  calc log⁺ (∑ t, f t)
  _ = log⁺ |∑ t, f t| := by
    rw [Real.logpos_abs]
  _ ≤ log⁺ (∑ t, |f t|) := by
    apply monotoneOn_logpos (by simp) (by simp [Finset.sum_nonneg])
    simp [Finset.abs_sum_le_sum_abs]
  _ ≤ log⁺ (∑ t : α, |f t_max|) := by
    apply monotoneOn_logpos (by simp [Finset.sum_nonneg]) (by simp [Finset.sum_nonneg]; positivity)
    exact Finset.sum_le_sum fun i a ↦ ht_max i
  _ = log⁺ (n * |f t_max|) := by
    simp [Finset.sum_const]
  _ ≤ log n + log⁺ |f t_max| := Real.logpos_mul_nat
  _ ≤ log n + ∑ t, log⁺ (f t) := by
    apply add_le_add (by rfl)
    rw [logpos_abs]
    exact Finset.single_le_sum (fun _ _ ↦ logpos_nonneg) (Finset.mem_univ t_max)
  sorry

theorem Real.logpos_sum {n : ℕ} (f : Fin n → ℝ) :
    log⁺ (∑ t, f t) ≤ log n + ∑ t, log⁺ (f t) := by
  -- Trivial case: empty sum
  by_cases hs : n = 0
  · simp [hs, Fin.isEmpty', logpos]
  -- Nontrivial case:
  -- Obtain maximal element…
  have nonEmpty := Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_ne_zero hs)
  obtain ⟨t_max, ht_max⟩ := Finite.exists_max (fun t ↦ |f t|)
  -- …then calculate
  calc log⁺ (∑ t, f t)
  _ = log⁺ |∑ t, f t| := by
    rw [Real.logpos_abs]
  _ ≤ log⁺ (∑ t, |f t|) := by
    apply monotoneOn_logpos (by simp) (by simp [Finset.sum_nonneg])
    simp [Finset.abs_sum_le_sum_abs]
  _ ≤ log⁺ (∑ t : Fin n, |f t_max|) := by
    apply monotoneOn_logpos (by simp [Finset.sum_nonneg]) (by simp [Finset.sum_nonneg]; positivity)
    exact Finset.sum_le_sum fun i a ↦ ht_max i
  _ = log⁺ (n * |f t_max|) := by
    simp [Finset.sum_const]
  _ ≤ log n + log⁺ |f t_max| := Real.logpos_mul_nat
  _ ≤ log n + ∑ t, log⁺ (f t) := by
    apply add_le_add (by rfl)
    rw [logpos_abs]
    exact Finset.single_le_sum (fun _ _ ↦ logpos_nonneg) (Finset.mem_univ t_max)

theorem Real.logpos_add {a b : ℝ} : log⁺ (a + b) ≤ log 2 + log⁺ a + log⁺ b := by
  convert logpos_sum (fun i => match i with | 0 => a | 1 => b : Fin 2 → ℝ) using 1
  <;> simp [add_assoc]
