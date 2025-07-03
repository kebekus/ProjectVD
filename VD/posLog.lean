import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import VD.harmonicAt_examples
import VD.harmonicAt_meanValue

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

lemma circleAverage_log_norm_sub_id_const_eq_posLog {a : ℂ} :
    circleAverage (log ‖· - a‖) 0 1 = log⁺ ‖a‖ := by
  rcases lt_trichotomy ‖a‖ 1 with h | h | h
  · -- ‖a‖ < 1
    sorry
  · -- ‖a‖ = 1
    sorry
  · -- ‖a‖ > 1
    sorry

-- Maximal 550 Zeilen

/-!
## Lemmas for the circleMap
-/

lemma circleMap_zero_one_add {x₁ x₂ : ℝ} :
    (circleMap 0 1 x₁) * (circleMap 0 1 x₂) = circleMap 0 1 (x₁+x₂) := by
  simp [circleMap, add_mul, Complex.exp_add]

/-!
## Computing `circleAverage (log ‖· - a‖) 0 1` in case where `‖a‖ < 1`.
-/

lemma l₂ {x : ℝ} {a : ℂ} : ‖(circleMap 0 1 x) - a‖ = ‖1 - (circleMap 0 1 (-x)) * a‖ := by
  calc ‖(circleMap 0 1 x) - a‖
  _ = 1 * ‖(circleMap 0 1 x) - a‖ := by
    exact Eq.symm (one_mul ‖circleMap 0 1 x - a‖)
  _ = ‖(circleMap 0 1 (-x))‖ * ‖(circleMap 0 1 x) - a‖ := by
    simp [norm_circleMap_zero]
  _ = ‖(circleMap 0 1 (-x)) * ((circleMap 0 1 x) - a)‖ := by
    exact Eq.symm (Complex.norm_mul (circleMap 0 1 (-x)) (circleMap 0 1 x - a))
  _ = ‖(circleMap 0 1 (-x)) * (circleMap 0 1 x) - (circleMap 0 1 (-x)) * a‖ := by
    rw [mul_sub]
  _ = ‖(circleMap 0 1 0) - (circleMap 0 1 (-x)) * a‖ := by
    rw [circleMap_zero_one_add]
    simp
  _ = ‖1 - (circleMap 0 1 (-x)) * a‖ := by
    congr
    simp [circleMap]

lemma xxx {a : ℂ} :
    circleAverage (log ‖· - a‖) 0 1 = circleAverage (log ‖1 - · * a‖) 0 1 := by
  sorry

lemma yy {a : ℂ} (ha : a ∈ Metric.ball 0 1) :
    HarmonicOn (log ‖1 - · * a‖) (Metric.closedBall 0 1) := by
  sorry

lemma int₀' {a : ℂ} (ha : a ∈ Metric.ball 0 1) :
    circleAverage (log ‖· - a‖) 0 1 = 0 := by
  rw [xxx]
  sorry

lemma int₀
  {a : ℂ}
  (ha : a ∈ Metric.ball 0 1) :
  circleAverage (log ‖· - a‖) 0 1 = 0 := by
  unfold circleAverage
  simp [pi_ne_zero]

  by_cases h₁a : a = 0
  · simp_all [circleAverage]

  -- case: a ≠ 0
  simp_rw [l₂]
  have {x : ℝ} : log ‖1 - circleMap 0 1 (-x) * a‖ = (fun w ↦ log ‖1 - circleMap 0 1 (w) * a‖) (-x) := by rfl
  conv =>
    left
    arg 1
    intro x
    rw [this]
  rw [intervalIntegral.integral_comp_neg ((fun w ↦ log ‖1 - circleMap 0 1 (w) * a‖))]

  let f₁ := fun w ↦ log ‖1 - circleMap 0 1 w * a‖
  have {x : ℝ} : log ‖1 - circleMap 0 1 x * a‖ = f₁ (x + 2 * π) := by
    dsimp [f₁]
    congr 4
    let A := periodic_circleMap 0 1 x
    simp at A
    exact id (Eq.symm A)
  conv =>
    left
    arg 1
    intro x
    rw [this]
  rw [intervalIntegral.integral_comp_add_right f₁ (2 * π)]
  simp
  dsimp [f₁]

  let ρ := ‖a‖⁻¹
  have hρ : 1 < ρ := by
    apply one_lt_inv_iff₀.mpr
    constructor
    · exact norm_pos_iff.mpr h₁a
    · exact mem_ball_zero_iff.mp ha

  let F := fun z ↦ log ‖1 - z * a‖

  have hf : ∀ x ∈ Metric.ball 0 ρ, HarmonicAt F x := by
    intro x hx
    apply logabs_of_holomorphicAt_is_harmonic
    apply Differentiable.holomorphicAt
    fun_prop
    apply sub_ne_zero_of_ne
    by_contra h
    have : ‖x * a‖ < 1 := by
      calc ‖x * a‖
      _ = ‖x‖ * ‖a‖ := by exact Complex.norm_mul x a
      _ < ρ * ‖a‖ := by
        apply (mul_lt_mul_right _).2
        exact mem_ball_zero_iff.mp hx
        exact norm_pos_iff.mpr h₁a
      _ = 1 := by
        dsimp [ρ]
        apply inv_mul_cancel₀
        exact norm_ne_zero_iff.mpr h₁a
    rw [← h] at this
    simp at this

  let A := harmonic_meanValue ρ 1 zero_lt_one hρ hf
  dsimp [F] at A
  simp at A
  exact A


lemma int''₁ {a : ℂ} {t₁ t₂ : ℝ} :
    IntervalIntegrable (log ‖circleMap 0 1 · - a‖) volume t₁ t₂ := by
  apply Function.Periodic.intervalIntegrable₀ _ two_pi_pos
  · apply circleIntegrable_log_norm_meromorphicOn (f := (· - a)) (fun _ _ ↦ by fun_prop)
  · rw [(by rfl : (log ‖circleMap 0 1 · - a‖) = (log ‖· - a‖) ∘ (circleMap 0 1))]
    apply (periodic_circleMap 0 1).comp

-- Integral of log ‖circleMap 0 1 x - 1‖

-- integral
lemma int₁₁ : ∫ (x : ℝ) in (0)..π, log (4 * sin x ^ 2) = 0 := by

  have t₀ : (fun x ↦ log (4 * sin x ^ 2)) =ᶠ[Filter.codiscreteWithin (Ι 0 π)]
        fun x ↦ log 4 + 2 * log (sin x) := by
    apply Filter.codiscreteWithin.mono (by tauto : Ι 0 π ⊆ Set.univ)
    have s₀ : AnalyticOnNhd ℝ (fun x ↦ (4 * sin x ^ 2)) Set.univ := by
      intro x hx
      fun_prop
    have s₁ := s₀.preimage_zero_mem_codiscrete (x := π / 2)
    simp only [sin_pi_div_two, one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      Set.preimage_compl, forall_const] at s₁
    filter_upwards [s₁] with a ha
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, mul_eq_zero,
      OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, false_or] at ha
    rw [log_mul (by norm_num) (by simp_all), log_pow, Nat.cast_ofNat]

  rw [intervalIntegral.integral_congr_codiscreteWithin t₀]
  rw [intervalIntegral.integral_add _root_.intervalIntegrable_const _ ]
  rw [intervalIntegral.integral_const_mul]
  simp
  rw [integral_log_sin_zero_pi]
  rw [(by norm_num : (4 : ℝ) = 2 * 2), log_mul two_ne_zero two_ne_zero]
  ring
  -- IntervalIntegrable (fun x => 2 * log (sin x)) volume 0 π
  apply intervalIntegrable_log_sin.const_mul 2

lemma logAffineHelper {x : ℝ} : log ‖circleMap 0 1 x - 1‖ = log (4 * sin (x / 2) ^ 2) / 2 := by
  rw [Complex.norm_def, log_sqrt (circleMap 0 1 x - 1).normSq_nonneg]
  congr
  calc Complex.normSq (circleMap 0 1 x - 1)
  _ = (cos x - 1) * (cos x - 1) + sin x * sin x := by
    dsimp [circleMap]
    rw [Complex.normSq_apply]
    simp
  _ = sin x ^ 2 + cos x ^ 2 + 1 - 2 * cos x := by
    ring
  _ = 2 - 2 * cos x := by
    rw [sin_sq_add_cos_sq]
    norm_num
  _ = 2 - 2 * cos (2 * (x / 2)) := by
    rw [← mul_div_assoc]
    congr
    norm_num
  _ = 4 - 4 * cos (x / 2) ^ 2 := by
    rw [cos_two_mul]
    ring
  _ = 4 * sin (x / 2) ^ 2 := by
    nth_rw 1 [← mul_one 4, ← sin_sq_add_cos_sq (x / 2)]
    ring

lemma int₁ :
  ∫ x in (0)..(2 * π), log ‖circleMap 0 1 x - 1‖ = 0 := by

  simp_rw [logAffineHelper]
  simp

  have : ∫ (x : ℝ) in (0)..2 * π, log (4 * sin (x / 2) ^ 2) =  2 * ∫ (x : ℝ) in (0)..π, log (4 * sin x ^ 2) := by
    have : 1 = 2 * (2 : ℝ)⁻¹ := by exact Eq.symm (mul_inv_cancel_of_invertible 2)
    nth_rw 1 [← one_mul (∫ (x : ℝ) in (0)..2 * π, log (4 * sin (x / 2) ^ 2))]
    rw [← mul_inv_cancel_of_invertible 2, mul_assoc]
    let f := fun y ↦ log (4 * sin y ^ 2)
    have {x : ℝ} : log (4 * sin (x / 2) ^ 2) = f (x / 2) := by simp [f]
    conv =>
      left
      right
      right
      arg 1
      intro x
      rw [this]
    rw [intervalIntegral.inv_mul_integral_comp_div]
    simp [f]
  rw [this]
  simp
  exact int₁₁

-- Integral of log ‖circleMap 0 1 x - a‖, for ‖a‖ = 1

-- integral
lemma int₂
  {a : ℂ}
  (ha : ‖a‖ = 1) :
  circleAverage (log ‖· - a‖) 0 1 = 0 := by
  unfold circleAverage
  simp [pi_ne_zero]

  simp_rw [l₂]
  have {x : ℝ} : log ‖1 - circleMap 0 1 (-x) * a‖ = (fun w ↦ log ‖1 - circleMap 0 1 (w) * a‖) (-x) := by rfl
  conv =>
    left
    arg 1
    intro x
    rw [this]
  rw [intervalIntegral.integral_comp_neg ((fun w ↦ log ‖1 - circleMap 0 1 (w) * a‖))]

  let f₁ := fun w ↦ log ‖1 - circleMap 0 1 w * a‖
  have {x : ℝ} : log ‖1 - circleMap 0 1 x * a‖ = f₁ (x + 2 * π) := by
    dsimp [f₁]
    congr 4
    let A := periodic_circleMap 0 1 x
    simp at A
    exact id (Eq.symm A)
  conv =>
    left
    arg 1
    intro x
    rw [this]
  rw [intervalIntegral.integral_comp_add_right f₁ (2 * π)]
  simp
  dsimp [f₁]

  have : ∃ ζ, a = circleMap 0 1 ζ := by
    apply Set.exists_range_iff.mp
    use a
    simp
    exact ha
  obtain ⟨ζ, hζ⟩ := this
  rw [hζ]
  simp_rw [circleMap_zero_one_add]

  rw [intervalIntegral.integral_comp_add_right (f := fun x ↦ log (norm (1 - circleMap 0 1 (x))))]

  have : Function.Periodic (fun x ↦ log (norm (1 - circleMap 0 1 x))) (2 * π) := by
    have : (fun x ↦ log (norm (1 - circleMap 0 1 x))) = ( (fun x ↦ log (norm (1 - x))) ∘ (circleMap 0 1) ) := by rfl
    rw [this]
    apply Function.Periodic.comp
    exact periodic_circleMap 0 1

  let A := Function.Periodic.intervalIntegral_add_eq this ζ 0
  simp at A
  simp
  rw [add_comm]
  rw [A]

  have {x : ℝ} : log (norm (1 - circleMap 0 1 x)) = log ‖circleMap 0 1 x - 1‖ := by
    congr 1
    exact norm_sub_rev 1 (circleMap 0 1 x)

  simp_rw [this]
  exact int₁



-- integral
lemma int₃ {a : ℂ} (ha : a ∈ Metric.closedBall 0 1) :
    circleAverage (log ‖· - a‖) 0 1 = 0 := by
  by_cases h₁a : a ∈ Metric.ball 0 1
  · exact int₀ h₁a
  · apply int₂
    simp at ha
    simp at h₁a
    linarith

-- integral
lemma int₄ {a : ℂ} {R : ℝ} (hR : 0 < R) (ha : a ∈ Metric.closedBall 0 R) :
    circleAverage (log ‖· - a‖) 0 R = log R := by
  have h₁a : a / R ∈ Metric.closedBall 0 1 := by
    simp
    simp at ha
    rw [div_le_comm₀]
    simp
    have : R = |R| := by
      exact Eq.symm (abs_of_pos hR)
    rwa [this] at ha
    rwa [abs_of_pos hR]
    simp

  have t₀ {x : ℝ} : circleMap 0 R x = R * circleMap 0 1 x := by
    unfold circleMap
    simp

  have {x : ℝ} : circleMap 0 R x - a = R * (circleMap 0 1 x - (a / R)) := by
    rw [t₀, mul_sub, mul_div_cancel₀]
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact hR.ne.symm

  have {x : ℝ} : circleMap 0 R x ≠ a → log ‖circleMap 0 R x - a‖ = log R + log ‖circleMap 0 1 x - (a / R)‖ := by
    intro hx
    rw [this]
    rw [norm_mul]
    rw [log_mul]
    congr
    --
    simpa using hR.le
    --
    simp
    exact hR.ne.symm
    --
    simp
    rw [t₀] at hx
    by_contra hCon
    rw [sub_eq_zero] at hCon
    rw [hCon] at hx
    simp at hx
    rw [mul_div_cancel₀] at hx
    tauto
    simp
    exact hR.ne.symm

  have : ∫ x in (0)..(2 * π), log ‖circleMap 0 R x - a‖ = ∫ x in (0)..(2 * π), log R + log ‖circleMap 0 1 x - (a / R)‖ := by
    rw [intervalIntegral.integral_congr_ae]
    rw [MeasureTheory.ae_iff]
    apply Set.Countable.measure_zero
    let A := (circleMap 0 R)⁻¹' { a }
    have s₀ : {a_1 | ¬(a_1 ∈ Ι 0 (2 * π) → log ‖circleMap 0 R a_1 - a‖ = log R + log ‖circleMap 0 1 a_1 - a / ↑R‖)} ⊆ A := by
      intro x
      contrapose
      intro hx
      unfold A at hx
      simp at hx
      simp
      intro h₂x
      let B := this hx
      simp at B
      rw [B]
    have s₁ : A.Countable := by
      apply Set.Countable.preimage_circleMap
      exact Set.countable_singleton a
      exact hR.ne.symm
    exact Set.Countable.mono s₀ s₁

  have aga : circleAverage (log ‖· - a‖) 0 R = log R + circleAverage (log ‖· - (a / R)‖) 0 1 := by
    unfold circleAverage
    rw [this]
    rw [intervalIntegral.integral_add]
    rw [intervalIntegral.integral_const]
    rw [smul_add]
    congr
    simp only [sub_zero, smul_eq_mul]
    ring_nf
    simp [pi_ne_zero]
    apply intervalIntegral.intervalIntegrable_const
    exact int''₁
  simp [aga, int₃ h₁a]

-- integral
lemma int₅ {a : ℂ} {R : ℝ} (ha : a ∈ Metric.closedBall 0 |R|) :
    circleAverage (log ‖· - a‖) 0 R = log R := by
  rcases lt_trichotomy 0 R with h | h | h
  · rw [int₄ h]
    ring_nf
    simp_all only [abs_of_pos h, Metric.mem_closedBall, dist_zero_right]
  · rw [eq_comm] at h
    simp_all
  · rw [← circleAverage_neg_radius, int₄ (Left.neg_pos_iff.mpr h)]
    ring_nf
    simp_all only [Metric.mem_closedBall, dist_zero_right, log_neg_eq_log]
    rwa [← abs_of_neg h]
