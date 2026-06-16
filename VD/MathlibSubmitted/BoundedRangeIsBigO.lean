/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Bounded Range versus `IsBigO` Asymptotics

For a continuous function `f : ℝ → E` into a seminormed space, having bounded range is equivalent to
being `O(1)` along both `atTop` and `atBot` (`Continuous.isBounded_range_iff_isBigO_atTop_atBot`).
For an even function a single `O(1)` bound along `atTop` already suffices
(`Continuous.isBounded_range_iff_isBigO_atTop_of_even`), since `Function.Even` transports an `atTop`
bound to an `atBot` bound (`Function.Even.isBigO_atBot_of_isBigO_atTop`).

## Implementation notes

These lemmas are intended for `Mathlib/Analysis/Asymptotics/SpecificAsymptotics.lean`, which
gathers specific asymptotic results that do not belong with the general theory developed in
`Mathlib/Analysis/Asymptotics/Defs.lean` and `Mathlib/Analysis/Asymptotics/Lemmas.lean`. All
imports they require are already available there.
-/

public section

open Asymptotics Bornology Filter Function Set

variable {E : Type*} [SeminormedAddCommGroup E]

/-- A continuous function `f : ℝ → E` has bounded range if and only if it is `O(1)`
at both `atTop` and `atBot`. -/
theorem Continuous.isBounded_range_iff_isBigO_atTop_atBot {f : ℝ → E} (hf : Continuous f) :
    IsBounded (range f) ↔ f =O[atTop] (1 : ℝ → ℝ) ∧ f =O[atBot] (1 : ℝ → ℝ) := by
  constructor <;> intro H
  · constructor
    all_goals
    · rw [isBigO_iff]
      obtain ⟨C, hC⟩ := H.exists_pos_norm_le
      exact ⟨C, by aesop⟩
  · obtain ⟨C₁, M₁, hC₁⟩ : ∃ C₁ M₁, ∀ x ≥ M₁, ‖f x‖ ≤ C₁ := by simp_all [isBigO_iff]
    obtain ⟨C₂, M₂, hC₂⟩ : ∃ C₂ M₂, ∀ x ≤ M₂, ‖f x‖ ≤ C₂ := by simp_all [isBigO_iff]
    obtain ⟨C₃, hC₃⟩ : ∃ C₃, ∀ x ∈ Icc M₂ M₁, ‖f x‖ ≤ C₃ :=
      isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
    rw [isBounded_iff_forall_norm_le]
    refine ⟨max C₁ (max C₂ C₃), forall_mem_range.2 fun x ↦ ?_⟩
    rcases le_total x M₁ with hx₁ | hx₁ <;> rcases le_total x M₂ with hx₂ | hx₂ <;> aesop

/-- An even function that is `O(1)` at `atTop` is also `O(1)` at `atBot`. -/
theorem Function.Even.isBigO_atBot_of_isBigO_atTop {f : ℝ → E} (heven : Function.Even f)
    (h : f =O[atTop] (1 : ℝ → ℝ)) : f =O[atBot] (1 : ℝ → ℝ) := by
  simp_all only [isBigO_iff, Pi.one_apply, norm_one, mul_one, eventually_atTop, eventually_atBot]
  obtain ⟨c, a, h⟩ := h
  exact ⟨c, -a, fun b hb ↦ by simpa [heven b] using h (-b) (by linarith)⟩

/-- A continuous even function `f : ℝ → E` has bounded range if and only if `f =O[atTop] 1`. -/
theorem Continuous.isBounded_range_iff_isBigO_atTop_of_even {f : ℝ → E} (hf : Continuous f)
    (heven : Function.Even f) :
    IsBounded (range f) ↔ f =O[atTop] (1 : ℝ → ℝ) :=
  ⟨fun h ↦ (hf.isBounded_range_iff_isBigO_atTop_atBot.mp h).1,
   fun h ↦ hf.isBounded_range_iff_isBigO_atTop_atBot.mpr ⟨h, heven.isBigO_atBot_of_isBigO_atTop h⟩⟩
