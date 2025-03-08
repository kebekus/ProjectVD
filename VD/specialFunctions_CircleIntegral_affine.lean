import Mathlib.MeasureTheory.Integral.Periodic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import VD.specialFunctions_Integral_log_sin
import VD.harmonicAt_examples
import VD.harmonicAt_meanValue
import VD.intervalIntegrability

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral



-- Lemmas for the circleMap

lemma l₀ {x₁ x₂ : ℝ} : (circleMap 0 1 x₁) * (circleMap 0 1 x₂) = circleMap 0 1 (x₁+x₂) := by
  dsimp [circleMap]
  simp
  rw [add_mul, Complex.exp_add]

lemma l₁ {x : ℝ} : ‖circleMap 0 1 x‖ = 1 := by
  rw [norm_circleMap_zero]
  simp

lemma l₂ {x : ℝ} : ‖(circleMap 0 1 x) - a‖ = ‖1 - (circleMap 0 1 (-x)) * a‖ := by
  calc ‖(circleMap 0 1 x) - a‖
  _ = 1 * ‖(circleMap 0 1 x) - a‖ := by
    exact Eq.symm (one_mul ‖circleMap 0 1 x - a‖)
  _ = ‖(circleMap 0 1 (-x))‖ * ‖(circleMap 0 1 x) - a‖ := by
    rw [l₁]
  _ = ‖(circleMap 0 1 (-x)) * ((circleMap 0 1 x) - a)‖ := by
    exact Eq.symm (NormedField.norm_mul' (circleMap 0 1 (-x)) (circleMap 0 1 x - a))
  _ = ‖(circleMap 0 1 (-x)) * (circleMap 0 1 x) - (circleMap 0 1 (-x)) * a‖ := by
    rw [mul_sub]
  _ = ‖(circleMap 0 1 0) - (circleMap 0 1 (-x)) * a‖ := by
    rw [l₀]
    simp
  _ = ‖1 - (circleMap 0 1 (-x)) * a‖ := by
    congr
    dsimp [circleMap]
    simp


-- Integral of log ‖circleMap 0 1 x - a‖, for ‖a‖ < 1.

lemma int'₀
  {a : ℂ}
  (ha : ‖a‖ ≠ 1) :
  IntervalIntegrable (fun x ↦ log ‖circleMap 0 1 x - a‖) volume 0 (2 * π) := by
  apply Continuous.intervalIntegrable
  apply Continuous.log
  fun_prop
  simp
  intro x
  by_contra h₁a
  rw [sub_eq_zero] at h₁a
  rw [← h₁a] at ha
  simp at ha


lemma int₀
  {a : ℂ}
  (ha : a ∈ Metric.ball 0 1) :
  ∫ (x : ℝ) in (0)..2 * π, log ‖circleMap 0 1 x - a‖ = 0 := by

  by_cases h₁a : a = 0
  · -- case: a = 0
    rw [h₁a]
    simp

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
      _ = ‖x‖ * ‖a‖ := by exact NormedField.norm_mul' x a
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


-- Integral of log ‖circleMap 0 1 x - 1‖

-- integral
lemma int₁₁ : ∫ (x : ℝ) in (0)..π, log (4 * sin x ^ 2) = 0 := by

  have t₁ {x : ℝ} : x ∈ Set.Ioo 0 π → log (4 * sin x ^ 2) = log 4 + 2 * log (sin x) := by
    intro hx
    rw [log_mul, log_pow]
    rfl
    exact (NeZero.ne' 4).symm
    apply pow_ne_zero 2
    apply (fun a => (ne_of_lt a).symm)
    exact sin_pos_of_mem_Ioo hx


  have t₂ : Set.EqOn (fun y ↦ log (4 * sin y ^ 2)) (fun y ↦ log 4 + 2 * log (sin y)) (Set.Ioo 0 π) := by
    intro x hx
    simp
    rw [t₁ hx]

  rw [intervalIntegral.integral_congr_volume pi_pos t₂]
  rw [intervalIntegral.integral_add]
  rw [intervalIntegral.integral_const_mul]
  simp
  rw [integral_log_sin₂]
  have : (4 : ℝ) = 2 * 2 := by norm_num
  rw [this, log_mul]
  ring
  norm_num
  norm_num
  -- IntervalIntegrable (fun x => log 4) volume 0 π
  simp
  -- IntervalIntegrable (fun x => 2 * log (sin x)) volume 0 π
  apply IntervalIntegrable.const_mul
  exact intervalIntegrable_log_sin

lemma logAffineHelper {x : ℝ} : log ‖circleMap 0 1 x - 1‖ = log (4 * sin (x / 2) ^ 2) / 2 := by
  rw [Complex.norm_def]
  rw [log_sqrt (Complex.normSq_nonneg (circleMap 0 1 x - 1))]
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
    congr; norm_num
  _ = 4 - 4 * cos (x / 2) ^ 2 := by
    rw [cos_two_mul]
    ring
  _ = 4 * sin (x / 2) ^ 2 := by
    nth_rw 1 [← mul_one 4, ← sin_sq_add_cos_sq (x / 2)]
    ring

lemma int'₁ : -- Integrability of log ‖circleMap 0 1 x - 1‖
  IntervalIntegrable (fun x ↦ log ‖circleMap 0 1 x - 1‖) volume 0 (2 * π) := by

  simp_rw [logAffineHelper]
  apply IntervalIntegrable.div_const
  rw [← IntervalIntegrable.comp_mul_left_iff (c := 2) (Ne.symm (NeZero.ne' 2))]
  simp

  have h₁ : Set.EqOn (fun x => log (4 * sin x ^ 2)) (fun x => log 4 + 2 * log (sin x)) (Set.Ioo 0 π) := by
    intro x hx
    simp [log_mul (Ne.symm (NeZero.ne' 4)), log_pow, ne_of_gt (sin_pos_of_mem_Ioo hx)]
  rw [IntervalIntegrable.integral_congr_Ioo pi_nonneg h₁]
  apply IntervalIntegrable.add
  simp
  apply IntervalIntegrable.const_mul
  exact intervalIntegrable_log_sin

lemma int''₁ : -- Integrability of log ‖circleMap 0 1 x - 1‖ for arbitrary intervals
  ∀ (t₁ t₂ : ℝ), IntervalIntegrable (fun x ↦ log ‖circleMap 0 1 x - 1‖) volume t₁ t₂ := by
  intro t₁ t₂

  apply Function.Periodic.intervalIntegrable₀ (T := 2 * π)
  --
  have : (fun x => log ‖circleMap 0 1 x - 1‖) = (fun x => log ‖x - 1‖) ∘ (circleMap 0 1) := rfl
  rw [this]
  apply Function.Periodic.comp
  exact periodic_circleMap 0 1
  --
  exact two_pi_pos
  --
  exact int'₁

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
    rw [intervalIntegral.inv_mul_integral_comp_div 2]
    simp [f]
  rw [this]
  simp
  exact int₁₁


-- Integral of log ‖circleMap 0 1 x - a‖, for ‖a‖ = 1

-- integrability
lemma int'₂
  {a : ℂ}
  (ha : ‖a‖ = 1) :
  IntervalIntegrable (fun x ↦ log ‖circleMap 0 1 x - a‖) volume 0 (2 * π) := by

  simp_rw [l₂]
  have {x : ℝ} : log ‖1 - circleMap 0 1 (-x) * a‖ = (fun w ↦ log ‖1 - circleMap 0 1 (w) * a‖) (-x) := by rfl
  conv =>
    arg 1
    intro x
    rw [this]
  rw [IntervalIntegrable.iff_comp_neg]

  let f₁ := fun w ↦ log ‖1 - circleMap 0 1 w * a‖
  have {x : ℝ} : log ‖1 - circleMap 0 1 x * a‖ = f₁ (x + 2 * π) := by
    dsimp [f₁]
    congr 4
    let A := periodic_circleMap 0 1 x
    simp at A
    exact id (Eq.symm A)
  conv =>
    arg 1
    intro x
    arg 0
    intro w
    rw [this]
  simp
  have : 0 = 2 * π - 2 * π := by ring
  rw [this]
  have : -(2 * π ) = 0 - 2 * π := by ring
  rw [this]
  apply IntervalIntegrable.comp_add_right _ (2 * π) --f₁ (2 * π)
  dsimp [f₁]

  have : ∃ ζ, a = circleMap 0 1 ζ := by
    apply Set.exists_range_iff.mp
    use a
    simp
    exact ha
  obtain ⟨ζ, hζ⟩ := this
  rw [hζ]
  simp_rw [l₀]

  have : 2 * π  = (2 * π + ζ) - ζ := by ring
  rw [this]
  have : 0 = ζ - ζ := by ring
  rw [this]
  have : (fun w => log (norm (1 - circleMap 0 1 (w + ζ)))) = fun x ↦ (fun w ↦ log (norm (1 - circleMap 0 1 (w)))) (x + ζ) := rfl
  rw [this]
  apply IntervalIntegrable.comp_add_right (f := (fun w ↦ log (norm (1 - circleMap 0 1 (w))))) _ ζ

  have : Function.Periodic (fun x ↦ log (norm (1 - circleMap 0 1 x))) (2 * π) := by
    have : (fun x ↦ log (norm (1 - circleMap 0 1 x))) = ( (fun x ↦ log (norm (1 - x))) ∘ (circleMap 0 1) ) := by rfl
    rw [this]
    apply Function.Periodic.comp
    exact periodic_circleMap 0 1

  let A := int''₁ (2 * π + ζ) ζ
  have {x : ℝ} : ‖circleMap 0 1 x - 1‖ = norm (1 - circleMap 0 1 x) := by
    exact norm_sub_rev (circleMap 0 1 x) 1
  simp_rw [this] at A
  exact A

-- integral
lemma int₂
  {a : ℂ}
  (ha : ‖a‖ = 1) :
  ∫ x in (0)..(2 * π), log ‖circleMap 0 1 x - a‖ = 0 := by

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
  simp_rw [l₀]

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
lemma int₃
  {a : ℂ}
  (ha : a ∈ Metric.closedBall 0 1) :
  ∫ x in (0)..(2 * π), log ‖circleMap 0 1 x - a‖ = 0 := by
  by_cases h₁a : a ∈ Metric.ball 0 1
  · exact int₀ h₁a
  · apply int₂
    simp at ha
    simp at h₁a
    linarith

-- integral
lemma int₄
  {a : ℂ}
  {R : ℝ}
  (hR : 0 < R)
  (ha : a ∈ Metric.closedBall 0 R) :
  ∫ x in (0)..(2 * π), log ‖circleMap 0 R x - a‖ = (2 * π) * log R := by

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

  rw [this]
  rw [intervalIntegral.integral_add]
  rw [int₃]
  rw [intervalIntegral.integral_const]
  simp
  --
  exact h₁a
  --
  apply intervalIntegral.intervalIntegrable_const
  --
  by_cases h₂a : ‖a / R‖ = 1
  · exact int'₂ h₂a
  · exact int'₀ h₂a


lemma intervalIntegrable_logAbs_circleMap_sub_const
  {a : ℂ}
  {r : ℝ}
  (hr : r ≠ 0) :
  IntervalIntegrable (fun x ↦ log ‖circleMap 0 r x - a‖) volume 0 (2 * π) := by

  have {z : ℂ} : z ≠ a → log ‖z - a‖ = log ‖r⁻¹ * z - r⁻¹ * a‖ + log ‖r‖ := by
    intro hz
    rw [← mul_sub, norm_mul]
    rw [log_mul (by simp [hr]) (by apply norm_ne_zero_iff.mpr; exact sub_ne_zero_of_ne hz)]
    simp

  have : (fun z ↦ log ‖z - a‖) =ᶠ[Filter.codiscreteWithin ⊤] (fun z ↦ log ‖r⁻¹ * z - r⁻¹ * a‖ + log ‖r‖) := by
    apply eventuallyEq_iff_exists_mem.mpr
    use {a}ᶜ
    constructor
    · simp_rw [mem_codiscreteWithin, Filter.disjoint_principal_right]
      simp
      intro y
      by_cases hy : y = a
      · rw [← hy]
        exact self_mem_nhdsWithin
      · refine mem_nhdsWithin.mpr ?_
        simp
        use {a}ᶜ
        constructor
        · exact isOpen_compl_singleton
        · constructor
          · tauto
          · tauto
    · intro x hx
      simp at hx
      apply this hx

  have hU : Metric.sphere (0 : ℂ) |r| ⊆ ⊤ := by
    exact fun ⦃a⦄ a => trivial
  let A := integrability_congr_changeDiscrete hU hr this

  have : (fun z => log ‖z - a‖) ∘ circleMap 0 r = (fun z => log ‖circleMap 0 r z - a‖) := by
    exact rfl
  rw [this] at A
  have : (fun z => log ‖r⁻¹ * z - r⁻¹ * a‖ + log ‖r‖) ∘ circleMap 0 r = (fun z => log ‖r⁻¹ * circleMap 0 r z - r⁻¹ * a‖ + log ‖r‖) := by
    exact rfl
  rw [this] at A
  rw [A]

  apply IntervalIntegrable.add _ intervalIntegrable_const
  have {x : ℝ} : r⁻¹ * circleMap 0 r x = circleMap 0 1 x := by
    unfold circleMap
    simp [hr]
  simp_rw [this]

  by_cases ha : ‖r⁻¹ * a‖ = 1
  · exact int'₂ ha
  · apply int'₀ ha
