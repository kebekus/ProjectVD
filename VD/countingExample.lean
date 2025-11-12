import Mathlib.Analysis.Complex.ValueDistribution.CountingFunction

open Function MeromorphicOn Metric Real Set Classical

namespace ValueDistribution

variable {α : Type*} [Zero α]

lemma coe_untop₀_of_ne_top' {a₁ : WithTop α} {a₂ : α} (h : a₂ ≠ 0) :
    a₁.untop₀ = a₂ ↔ a₁ = a₂ := by
  constructor
  · intro h₁
    by_cases h₂ : a₁ = ⊤
    · simp_all
    · lift a₁ to α using h₂
      simp_all
  · intro h
    simp [h]

example : logCounting (fun z ↦ z : ℂ → ℂ) 0 = log := by
  simp [logCounting]
  have : divisor (fun z ↦ z : ℂ → ℂ) univ = (fun z ↦ if z = 0 then 1 else 0 : ℂ → ℤ) := by
    ext z
    rw [divisor_apply (fun _ _ ↦ by fun_prop) (by tauto)]
    by_cases h : z = 0
    · simp_all
      refine (coe_untop₀_of_ne_top' ?_).mpr ?_
      simp
      refine (meromorphicOrderAt_eq_int_iff ?_).mpr ?_
      fun_prop
      use 1
      simp_all
      have : (1 : ℂ → ℂ) = fun _ ↦ 1 := by rfl
      simp_all
      fun_prop
    · simp_all
      left
      refine (meromorphicOrderAt_eq_int_iff ?_).mpr ?_
      fun_prop
      use fun z ↦ z
      simp_all
      fun_prop
  simp [locallyFinsuppWithin.logCounting]
  ext r
  rw [finsum_eq_zero_of_forall_eq_zero]
  simp_all
  · intro z
    by_cases h : z = 0
    · simp_all
    · simp_all
      left
      simp [locallyFinsuppWithin.toClosedBall]
      rw [locallyFinsuppWithin.restrict_apply]
      simp
      intro hz
      simp_all

example : logCounting (fun z ↦ z⁻¹ : ℂ → ℂ) 0 = 0 := by
  simp [logCounting]
  have : divisor (fun z ↦ z⁻¹ : ℂ → ℂ) univ = (fun z ↦ if z = 0 then -1 else 0 : ℂ → ℤ) := by
    ext z
    rw [divisor_apply (fun _ _ ↦ by fun_prop) (by tauto)]
    by_cases h : z = 0
    · simp_all
      refine (coe_untop₀_of_ne_top' ?_).mpr ?_
      simp
      refine (meromorphicOrderAt_eq_int_iff ?_).mpr ?_
      fun_prop
      use 1
      simp_all
      have : (1 : ℂ → ℂ) = fun _ ↦ 1 := by rfl
      simp_all
      fun_prop
    · simp_all
      left
      refine (meromorphicOrderAt_eq_int_iff ?_).mpr ?_
      fun_prop
      use fun z ↦ z⁻¹
      simp_all
      apply analyticAt_inv
      assumption
  simp [locallyFinsuppWithin.logCounting]
  ext r
  rw [finsum_eq_zero_of_forall_eq_zero]
  simp_all
  · intro z
    by_cases h : z = 0
    · simp_all
    · simp_all
      left
      --rw [posPart_apply]
      simp [locallyFinsuppWithin.toClosedBall]
      rw [locallyFinsuppWithin.restrict_apply]
      simp
      intro hz
      simp_all

example : logCounting (fun _ ↦ 1 : ℂ → ℂ) 0 = 0 := by
  simp [logCounting]

end ValueDistribution
