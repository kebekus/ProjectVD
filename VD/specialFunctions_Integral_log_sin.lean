import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import VD.meromorphicOn_integrability
import Mathlib.Analysis.Complex.CauchyIntegral

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

theorem analyticOnNhd_realPart {f : ℂ → ℂ} (h : AnalyticOnNhd ℂ f Set.univ) :
    AnalyticOnNhd ℝ (fun x ↦ (f x).re : ℝ → ℝ) Set.univ := by
  have : (fun x ↦ (f x).re : ℝ → ℝ) = Complex.reCLM ∘ f ∘ Complex.ofRealCLM := by
    ext x
    tauto
  rw [this]
  apply ContinuousLinearMap.comp_analyticOnNhd Complex.reCLM
  apply AnalyticOnNhd.comp'
  apply AnalyticOnNhd.mono (t := Set.univ)
  apply AnalyticOnNhd.restrictScalars (𝕜' := ℂ)
  exact h
  tauto
  exact ContinuousLinearMap.analyticOnNhd Complex.ofRealCLM Set.univ

theorem analyticOnNhd_sin :
    AnalyticOnNhd ℝ Real.sin Set.univ := by
  apply analyticOnNhd_realPart (f := Complex.sin)
  apply Complex.analyticOnNhd_univ_iff_differentiable.mpr
  exact Complex.differentiable_sin

theorem intervalIntegrable_log_sin {a b : ℝ} :
    IntervalIntegrable (log ∘ sin) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log
  apply AnalyticOnNhd.meromorphicOn
  apply analyticOnNhd_sin.mono
  tauto

theorem intervalIntegrable_log_cos : IntervalIntegrable (log ∘ cos) volume 0 (π / 2) := by
  let A := IntervalIntegrable.comp_sub_left (intervalIntegrable_log_sin (a := 0) (b := π / 2)) (π / 2)
  simp only [Function.comp_apply, sub_zero, sub_self] at A
  simp_rw [sin_pi_div_two_sub] at A
  have : (fun x => log (cos x)) = log ∘ cos := rfl
  apply IntervalIntegrable.symm
  rwa [← this]

theorem intervalIntegral.integral_congr_volume
  {E : Type u_3} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E}
  {g : ℝ → E}
  {a : ℝ}
  {b : ℝ}
  (h₀ : a < b)
  (h₁ : Set.EqOn f g (Set.Ioo a b)) :
  ∫ (x : ℝ) in a..b, f x = ∫ (x : ℝ) in a..b, g x := by

  apply intervalIntegral.integral_congr_ae
  rw [MeasureTheory.ae_iff]
  apply nonpos_iff_eq_zero.1
  push_neg
  have : {x | x ∈ Ι a b ∧ f x ≠ g x} ⊆ {b} := by
    intro x hx
    have t₂ : x ∈ Ι a b \ Set.Ioo a b := by
      constructor
      · exact hx.1
      · by_contra H
        exact hx.2 (h₁ H)
    rw [Set.uIoc_of_le h₀.le] at t₂
    rw [Set.Ioc_diff_Ioo_same h₀] at t₂
    assumption
  calc volume {a_1 | a_1 ∈ Ι a b ∧ f a_1 ≠ g a_1}
  _ ≤ volume {b} := volume.mono this
  _ = 0 := volume_singleton

theorem IntervalIntegrable.integral_congr_Ioo
  {E : Type u_3} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : ℝ → E}
  {a b : ℝ}
  (hab : a ≤ b)
  (hfg : Set.EqOn f g (Set.Ioo a b)) :
  IntervalIntegrable f volume a b ↔ IntervalIntegrable g volume a b := by

  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  rw [MeasureTheory.integrableOn_congr_fun hfg measurableSet_Ioo]
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hab]

lemma integral_log_sin₀ : ∫ (x : ℝ) in (0)..π, log (sin x) = 2 * ∫ (x : ℝ) in (0)..(π / 2), log (sin x) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := π / 2) (c := π)]
  conv =>
    left
    right
    arg 1
    intro x
    rw [← sin_pi_sub]
  rw [intervalIntegral.integral_comp_sub_left (fun x ↦ log (sin x)) π]
  have : π - π / 2 = π / 2 := by linarith
  rw [this]
  simp
  ring
  -- IntervalIntegrable (fun x => log (sin x)) volume 0 (π / 2)
  exact intervalIntegrable_log_sin
  -- IntervalIntegrable (fun x => log (sin x)) volume (π / 2) π
  exact intervalIntegrable_log_sin

lemma integral_log_sin₁ : ∫ (x : ℝ) in (0)..(π / 2), log (sin x) = -log 2 * π/2 := by

  have t₁ {x : ℝ} : x ∈ Set.Ioo 0 (π / 2) → log (sin (2 * x)) = log 2 + log (sin x) + log (cos x) := by
    intro hx
    simp at hx

    rw [sin_two_mul x, log_mul, log_mul]
    exact Ne.symm (NeZero.ne' 2)
    -- sin x ≠ 0
    apply (fun a => (ne_of_lt a).symm)
    apply sin_pos_of_mem_Ioo
    constructor
    · exact hx.1
    · linarith [pi_pos, hx.2]
    -- 2 * sin x ≠ 0
    simp
    apply (fun a => (ne_of_lt a).symm)
    apply sin_pos_of_mem_Ioo
    constructor
    · exact hx.1
    · linarith [pi_pos, hx.2]
    -- cos x ≠ 0
    apply (fun a => (ne_of_lt a).symm)
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [pi_pos, hx.1]
    · exact hx.2

  have t₂ : Set.EqOn (fun y ↦ log (sin y)) (fun y ↦ log (sin (2 * y)) - log 2 - log (cos y)) (Set.Ioo 0 (π / 2)) := by
    intro x hx
    simp
    rw [t₁ hx]
    ring

  rw [intervalIntegral.integral_congr_volume _ t₂]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub]
  rw [intervalIntegral.integral_const]
  rw [intervalIntegral.integral_comp_mul_left (c := 2) (f := fun x ↦ log (sin x))]
  simp
  have : 2 * (π / 2) = π := by linarith
  rw [this]
  rw [integral_log_sin₀]

  have : ∫ (x : ℝ) in (0)..(π / 2), log (sin x) = ∫ (x : ℝ) in (0)..(π / 2), log (cos x) := by
    conv =>
      right
      arg 1
      intro x
      rw [← sin_pi_div_two_sub]
    rw [intervalIntegral.integral_comp_sub_left (fun x ↦ log (sin x)) (π / 2)]
    simp
  rw [← this]
  simp
  linarith

  exact Ne.symm (NeZero.ne' 2)
  -- IntervalIntegrable (fun x => log (sin (2 * x))) volume 0 (π / 2)
  let A := (intervalIntegrable_log_sin (a := 0) (b := π)).comp_mul_left 2
  simp at A
  assumption
  -- IntervalIntegrable (fun x => log 2) volume 0 (π / 2)
  simp
  -- IntervalIntegrable (fun x => log (sin (2 * x)) - log 2) volume 0 (π / 2)
  apply IntervalIntegrable.sub
  -- -- IntervalIntegrable (fun x => log (sin (2 * x))) volume 0 (π / 2)
  let A := (intervalIntegrable_log_sin (a := 0) (b := π)).comp_mul_left 2
  simp at A
  assumption
  -- -- IntervalIntegrable (fun x => log 2) volume 0 (π / 2)
  simp
  -- -- IntervalIntegrable (fun x => log (cos x)) volume 0 (π / 2)
  exact intervalIntegrable_log_cos
  --
  linarith [pi_pos]


lemma integral_log_sin₂ : ∫ (x : ℝ) in (0)..π, log (sin x) = -log 2 * π := by
  rw [integral_log_sin₀, integral_log_sin₁]
  ring
