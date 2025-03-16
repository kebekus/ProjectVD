import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral



lemma logsinBound : ∀ x ∈ (Set.Icc 0 1), ‖(log ∘ sin) x‖ ≤ ‖log ((π / 2)⁻¹ * x)‖ := by

  intro x hx
  by_cases h'x : x = 0
  · rw [h'x]; simp

  -- Now handle the case where x ≠ 0
  have l₀ : log ((π / 2)⁻¹ * x) ≤ 0 := by
    apply log_nonpos
    norm_num [pi_pos]
    exact hx.1
    --
    simp
    apply mul_le_one₀ _ hx.1 hx.2
    rw [div_le_one pi_pos]
    exact two_le_pi

  have l₁ : 0 ≤ sin x := by
    apply sin_nonneg_of_nonneg_of_le_pi (Set.mem_Icc.1 hx).1
    trans (1 : ℝ)
    exact (Set.mem_Icc.1 hx).2
    trans π / 2
    exact one_le_pi_div_two
    norm_num [pi_nonneg]
  have l₂ : log (sin x) ≤ 0 := log_nonpos l₁ (sin_le_one x)

  simp only [norm_eq_abs, Function.comp_apply]
  rw [abs_eq_neg_self.2 l₀]
  rw [abs_eq_neg_self.2 l₂]
  simp only [neg_le_neg_iff, ge_iff_le]

  have l₃ : x ∈ (Set.Ioi 0) := by
    simp
    exact lt_of_le_of_ne (Set.mem_Icc.1 hx).1 ( fun a => h'x (id (Eq.symm a)) )

  have l₅ : 0 < (π / 2)⁻¹ * x := by
    apply mul_pos
    apply inv_pos.2
    apply div_pos pi_pos zero_lt_two
    exact l₃

  have : ∀ x ∈ (Set.Icc 0 (π / 2)), (π / 2)⁻¹ * x ≤ sin x := by
    intro x hx

    have i₀ : 0 ∈ Set.Icc 0 π :=
      Set.left_mem_Icc.mpr pi_nonneg
    have i₁ : π / 2 ∈ Set.Icc 0 π :=
      Set.mem_Icc.mpr ⟨div_nonneg pi_nonneg zero_le_two, half_le_self pi_nonneg⟩

    have i₂ : 0 ≤ 1 - (π / 2)⁻¹ * x := by
      rw [sub_nonneg]
      calc (π / 2)⁻¹ * x
      _ ≤ (π / 2)⁻¹ * (π / 2) := by
        apply mul_le_mul_of_nonneg_left
        exact (Set.mem_Icc.1 hx).2
        apply inv_nonneg.mpr (div_nonneg pi_nonneg zero_le_two)
      _ = 1 := by
        apply inv_mul_cancel₀
        apply div_ne_zero_iff.mpr
        constructor
        · exact pi_ne_zero
        · exact Ne.symm (NeZero.ne' 2)

    have i₃ : 0 ≤ (π / 2)⁻¹ * x := by
      apply mul_nonneg
      apply inv_nonneg.2
      apply div_nonneg
      exact pi_nonneg
      exact zero_le_two
      exact (Set.mem_Icc.1 hx).1

    have i₄ : 1 - (π / 2)⁻¹ * x + (π / 2)⁻¹ * x = 1 := by ring

    let B := strictConcaveOn_sin_Icc.concaveOn.2 i₀ i₁ i₂ i₃ i₄
    simp [Real.sin_pi_div_two] at B
    rw [(by ring_nf; rw [mul_inv_cancel₀ pi_ne_zero, one_mul] : 2 / π * x * (π / 2) = x)] at B
    simpa

  apply log_le_log l₅
  apply this
  apply Set.mem_Icc.mpr
  constructor
  · exact l₃.le
  · trans 1
    exact (Set.mem_Icc.1 hx).2
    exact one_le_pi_div_two



lemma intervalIntegrable_log_sin₁ : IntervalIntegrable (log ∘ sin) volume 0 1 := by


  have int_log : IntervalIntegrable (fun x ↦ ‖log ((π / 2)⁻¹ * x)‖) volume 0 1 := by
    have int_log : IntervalIntegrable (fun x ↦ ‖log x‖) volume 0 1 :=
      intervalIntegrable_log'.norm

    have A := IntervalIntegrable.comp_mul_right int_log (π / 2)⁻¹
    simp only [norm_eq_abs] at A
    conv =>
      arg 1
      intro x
      rw [mul_comm]
    simp only [norm_eq_abs]
    apply IntervalIntegrable.mono A
    simp
    trans Set.Icc 0 (π / 2)
    exact Set.Icc_subset_Icc (Preorder.le_refl 0) one_le_pi_div_two
    exact Set.Icc_subset_uIcc
    exact Preorder.le_refl volume

  apply IntervalIntegrable.mono_fun' (g := fun x ↦ ‖log ((π / 2)⁻¹ * x)‖)
  exact int_log

  -- AEStronglyMeasurable (log ∘ sin) (volume.restrict (Ι 0 1))
  apply ContinuousOn.aestronglyMeasurable
  apply ContinuousOn.comp (t := Ι 0 1)
  apply ContinuousOn.mono (s := {0}ᶜ)
  exact continuousOn_log
  intro x hx
  by_contra contra
  simp at contra
  rw [contra, Set.left_mem_uIoc] at hx
  linarith
  exact continuousOn_sin

  -- Set.MapsTo sin (Ι 0 1) (Ι 0 1)
  rw [Set.uIoc_of_le (zero_le_one' ℝ)]
  exact fun x hx ↦ ⟨sin_pos_of_pos_of_le_one hx.1 hx.2, sin_le_one x⟩

  -- MeasurableSet (Ι 0 1)
  exact measurableSet_uIoc

  -- (fun x => ‖(log ∘ sin) x‖) ≤ᶠ[ae (volume.restrict (Ι 0 1))] ‖log‖
  dsimp [EventuallyLE]
  rw [MeasureTheory.ae_restrict_iff]
  apply MeasureTheory.ae_of_all
  intro x hx
  have : x ∈ Set.Icc 0 1 := by
    simp
    simp at hx
    constructor
    · exact hx.1.le
    · exact hx.2
  let A := logsinBound x this
  simp only [Function.comp_apply, norm_eq_abs] at A
  exact A

  apply measurableSet_le
  apply Measurable.comp'
  exact continuous_abs.measurable
  exact Measurable.comp' measurable_log continuous_sin.measurable
  -- Measurable fun a => |log ((π / 2)⁻¹ * a)|
  apply Measurable.comp'
  exact continuous_abs.measurable
  apply Measurable.comp'
  exact measurable_log
  exact measurable_const_mul (π / 2)⁻¹

lemma intervalIntegrable_log_sin₂ : IntervalIntegrable (log ∘ sin) volume 0 (π / 2) := by

  apply IntervalIntegrable.trans (b := 1)
  exact intervalIntegrable_log_sin₁

  -- IntervalIntegrable (log ∘ sin) volume 1 (π / 2)
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.comp continuousOn_log continuousOn_sin
  intro x hx
  rw [Set.uIcc_of_le, Set.mem_Icc] at hx
  have : 0 < sin x := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · calc 0
      _ < 1 := Real.zero_lt_one
      _ ≤ x := hx.1
    · calc x
      _ ≤ π / 2 := hx.2
      _ < π := div_two_lt_of_pos pi_pos
  by_contra h₁x
  simp at h₁x
  rw [h₁x] at this
  simp at this
  exact one_le_pi_div_two

theorem intervalIntegrable_log_sin : IntervalIntegrable (log ∘ sin) volume 0 π := by
  apply IntervalIntegrable.trans (b := π / 2)
  exact intervalIntegrable_log_sin₂
  -- IntervalIntegrable (log ∘ sin) volume (π / 2) π
  have B := (IntervalIntegrable.comp_sub_left intervalIntegrable_log_sin₂ π).symm
  simp at B
  have : π - π / 2 = π / 2 := by linarith
  rwa [this] at B

theorem intervalIntegrable_log_cos : IntervalIntegrable (log ∘ cos) volume 0 (π / 2) := by
  let A := IntervalIntegrable.comp_sub_left intervalIntegrable_log_sin₂ (π / 2)
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
  exact intervalIntegrable_log_sin₂
  -- IntervalIntegrable (fun x => log (sin x)) volume (π / 2) π
  apply intervalIntegrable_log_sin.mono_set
  rw [Set.uIcc_of_le, Set.uIcc_of_le]
  apply Set.Icc_subset_Icc_left
  linarith [pi_pos]
  linarith [pi_pos]
  linarith [pi_pos]


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
  let A := intervalIntegrable_log_sin.comp_mul_left 2
  simp at A
  assumption
  -- IntervalIntegrable (fun x => log 2) volume 0 (π / 2)
  simp
  -- IntervalIntegrable (fun x => log (sin (2 * x)) - log 2) volume 0 (π / 2)
  apply IntervalIntegrable.sub
  -- -- IntervalIntegrable (fun x => log (sin (2 * x))) volume 0 (π / 2)
  let A := intervalIntegrable_log_sin.comp_mul_left 2
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
