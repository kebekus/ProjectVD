import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.CircleIntegral
import VD.meromorphicOn_integrability
import VD.stronglyMeromorphic_JensenFormula
import VD.ToMathlib.CountingFunction

open Real


-- Lang p. 164

theorem MeromorphicOn.restrict
  {f : ℂ → ℂ}
  (h₁f : MeromorphicOn f ⊤)
  (r : ℝ) :
  MeromorphicOn f (Metric.closedBall 0 r) := by
  exact fun x a => h₁f x trivial

theorem MeromorphicOn.restrict_inv
  {f : ℂ → ℂ}
  (h₁f : MeromorphicOn f ⊤)
  (r : ℝ) :
  h₁f.inv.restrict r = (h₁f.restrict r).inv := by
  funext x
  simp



--

noncomputable def MeromorphicOn.m_infty
  {f : ℂ → ℂ}
  (_ : MeromorphicOn f ⊤) :
  ℝ → ℝ :=
  fun r ↦ (2 * π)⁻¹ * ∫ x in (0)..(2 * π), log⁺ ‖f (circleMap 0 r x)‖

theorem Nevanlinna_proximity
  {f : ℂ → ℂ}
  {r : ℝ}
  (h₁f : MeromorphicOn f ⊤) :
  (2 * π)⁻¹ * ∫ x in (0)..(2 * π), log ‖f (circleMap 0 r x)‖ = (h₁f.m_infty r) - (h₁f.inv.m_infty r) := by

  unfold MeromorphicOn.m_infty
  rw [← mul_sub]; congr
  rw [← intervalIntegral.integral_sub]; congr
  funext x
  simp_rw [← posLog_sub_posLog_inv]; congr
  exact Eq.symm (IsAbsoluteValue.abv_inv Norm.norm (f (circleMap 0 r x)))
  --
  apply MeromorphicOn.circleIntegrable_posLog_norm
  intro z hx
  exact h₁f z trivial
  --
  apply MeromorphicOn.circleIntegrable_posLog_norm
  exact MeromorphicOn.inv_iff.mpr fun x a => h₁f x trivial

noncomputable def MeromorphicOn.T_infty
  {f : ℂ → ℂ}
  (hf : MeromorphicOn f ⊤) :
  ℝ → ℝ :=
  hf.m_infty + VD.logCounting f ⊤


theorem Nevanlinna_firstMain₁
  {f : ℂ → ℂ}
  (h₁f : MeromorphicOn f ⊤)
  (h₂f : MeromorphicNFAt f 0)
  (h₃f : f 0 ≠ 0) :
  (fun _ ↦ log ‖f 0‖) + h₁f.inv.T_infty = h₁f.T_infty := by
  classical

  rw [add_eq_of_eq_sub]
  unfold MeromorphicOn.T_infty

  have {A B C D : ℝ → ℝ} : A + B - (C + D) = A - C - (D - B) := by
    ring
  rw [this]
  clear this

  rw [← VD.logCounting_inv]
  rw [← VD.log_counting_zero_sub_logCounting_top]
  unfold Function.locallyFinsuppWithin.logCounting
  have XX {r : ℝ} : (MeromorphicOn.divisor f ⊤).toBall r  = MeromorphicOn.divisor f (Metric.closedBall 0 |r|) := by
    unfold Function.locallyFinsuppWithin.toBall
    exact MeromorphicOn.divisor_restrict h₁f fun ⦃a⦄ a ↦ trivial
  simp_all
  clear XX
  have ZZ : (MeromorphicOn.divisor f Set.univ) 0 = 0 := by
    rw [MeromorphicOn.divisor_apply]
    simp_rw [← h₂f.order_eq_zero_iff] at h₃f
    simp_rw [h₃f]
    exact rfl
    assumption
    trivial
  rw [ZZ]
  simp
  funext r
  simp
  rw [← Nevanlinna_proximity h₁f]

  by_cases h₁r : r = 0
  rw [h₁r]
  simp
  have : π⁻¹ * 2⁻¹ * (2 * π * log (norm (f 0))) = (π⁻¹ * (2⁻¹ * 2) * π) * log (norm (f 0)) := by
    ring
  rw [this]
  clear this
  simp [pi_ne_zero]

  by_cases hr : 0 < r
  let A := jensen hr f (h₁f.restrict r) h₂f h₃f
  simp at A
  rw [A]
  clear A
  simp
  have {A B : ℝ} : -A + B = B - A := by ring
  rw [this]
  have : |r| = r := by
    rw [← abs_of_pos hr]
    simp
  rw [this]

  -- case 0 < -r
  have h₂r : 0 < -r := by
    simp [h₁r, hr]
    by_contra hCon
    -- Assume ¬(r < 0), which means r >= 0
    push_neg at hCon
    -- Now h is r ≥ 0, so we split into cases
    rcases lt_or_eq_of_le hCon with h|h
    · tauto
    · tauto
  let A := jensen h₂r f (h₁f.restrict (-r)) h₂f h₃f
  simp at A
  rw [A]
  clear A
  simp
  have {A B : ℝ} : -A + B = B - A := by ring
  rw [this]

  congr 1
  congr 1
  let A := integrabl_congr_negRadius (f := (fun z ↦ log (norm (f z)))) (r := r)
  rw [A]
  have : |r| = -r := by
    rw [← abs_of_pos h₂r]
    simp
  rw [this]


theorem Nevanlinna_firstMain₂
  {f : ℂ → ℂ}
  {a : ℂ}
  {r : ℝ}
  (h₁f : MeromorphicOn f ⊤) :
  |(h₁f.T_infty r) - ((h₁f.sub (MeromorphicOn.const a)).T_infty r)| ≤ posLog ‖a‖ + log 2 := by

  -- See Lang, p. 168

  have : (h₁f.T_infty r) - ((h₁f.sub (MeromorphicOn.const a)).T_infty r) = (h₁f.m_infty r) - ((h₁f.sub (MeromorphicOn.const a)).m_infty r) := by
    unfold MeromorphicOn.T_infty
    rw [VD.logCounting_sub_const_right h₁f]
    simp
  rw [this]
  clear this

  unfold MeromorphicOn.m_infty
  rw [←mul_sub]
  rw [←intervalIntegral.integral_sub]

  let g := f - (fun _ ↦ a)

  have t₀₀ (x : ℝ) : log⁺ ‖f (circleMap 0 r x)‖ ≤ log⁺ ‖g (circleMap 0 r x)‖ + log⁺ ‖a‖ + log 2 := by
    unfold g
    simp only [Pi.sub_apply]

    calc log⁺ ‖f (circleMap 0 r x)‖
    _ = log⁺ ‖g (circleMap 0 r x) + a‖ := by
      unfold g
      simp
    _ ≤ log⁺ (‖g (circleMap 0 r x)‖ + ‖a‖) := by
      apply monotoneOn_posLog
      refine Set.mem_Ici.mpr ?_
      apply norm_nonneg
      refine Set.mem_Ici.mpr ?_
      apply add_nonneg
      apply norm_nonneg
      apply norm_nonneg
      --
      apply norm_add_le
    _ ≤ log⁺ ‖g (circleMap 0 r x)‖ + log⁺ ‖a‖ + log 2 := by
      convert posLog_add using 1
      ring


  have t₁₀ (x : ℝ) : log⁺ ‖f (circleMap 0 r x)‖ - log⁺ ‖g (circleMap 0 r x)‖ ≤ log⁺ ‖a‖ + log 2 := by
    rw [sub_le_iff_le_add]
    nth_rw 1 [add_comm]
    rw [←add_assoc]
    apply t₀₀ x
  clear t₀₀

  have t₀₁ (x : ℝ) : log⁺ ‖g (circleMap 0 r x)‖ ≤ log⁺ ‖f (circleMap 0 r x)‖ + log⁺ ‖a‖ + log 2 := by
    unfold g
    simp only [Pi.sub_apply]

    calc log⁺ ‖g (circleMap 0 r x)‖
    _ = log⁺ ‖f (circleMap 0 r x) - a‖ := by
      unfold g
      simp
    _ ≤ log⁺ (‖f (circleMap 0 r x)‖ + ‖a‖) := by
      apply monotoneOn_posLog
      refine Set.mem_Ici.mpr ?_
      apply norm_nonneg
      refine Set.mem_Ici.mpr ?_
      apply add_nonneg
      apply norm_nonneg
      apply norm_nonneg
      --
      apply norm_sub_le
    _ ≤ log⁺ ‖f (circleMap 0 r x)‖ + log⁺ ‖a‖ + log 2 := by
      convert posLog_add using 1
      ring

  have t₁₁ (x : ℝ) : log⁺ ‖g (circleMap 0 r x)‖ - log⁺ ‖f (circleMap 0 r x)‖ ≤ log⁺ ‖a‖ + log 2 := by
    rw [sub_le_iff_le_add]
    nth_rw 1 [add_comm]
    rw [←add_assoc]
    apply t₀₁ x
  clear t₀₁

  have t₂ {x : ℝ} : ‖log⁺ ‖f (circleMap 0 r x)‖ - log⁺ ‖g (circleMap 0 r x)‖‖ ≤ log⁺ ‖a‖ + log 2 := by
    by_cases h : 0 ≤ log⁺ ‖f (circleMap 0 r x)‖ - log⁺ ‖g (circleMap 0 r x)‖
    · rw [norm_of_nonneg h]
      exact t₁₀ x
    · rw [norm_of_nonpos (by linarith)]
      rw [neg_sub]
      exact t₁₁ x
  clear t₁₀ t₁₁

  have s₀ : ‖∫ (x : ℝ) in (0)..(2 * π), log⁺ ‖f (circleMap 0 r x)‖ - log⁺ ‖g (circleMap 0 r x)‖‖ ≤ (log⁺ ‖a‖ + log 2) * |2 * π - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    exact t₂
  clear t₂
  simp only [norm_eq_abs, sub_zero] at s₀
  rw [abs_mul]

  have s₁ : |(2 * π)⁻¹| * |∫ (x : ℝ) in (0)..(2 * π), log⁺ ‖f (circleMap 0 r x)‖ - log⁺ ‖g (circleMap 0 r x)‖| ≤ |(2 * π)⁻¹| * ((log⁺ ‖a‖ + log 2) * |2 * π|) := by
    apply mul_le_mul_of_nonneg_left
    exact s₀
    apply abs_nonneg
  have : |(2 * π)⁻¹| * ((log⁺ ‖a‖ + log 2) * |2 * π|) = log⁺ ‖a‖ + log 2 := by
    rw [mul_comm, mul_assoc]
    have : |2 * π| * |(2 * π)⁻¹| = 1 := by
      rw [abs_mul, abs_inv, abs_mul]
      rw [abs_of_pos pi_pos]
      simp [pi_ne_zero]
      ring_nf
      simp [pi_ne_zero]
    rw [this]
    simp
  rw [this] at s₁
  assumption
  --
  apply MeromorphicOn.circleIntegrable_posLog_norm
  exact fun x a => h₁f x trivial
  --
  apply MeromorphicOn.circleIntegrable_posLog_norm
  apply MeromorphicOn.sub
  exact fun x a => h₁f x trivial
  apply MeromorphicOn.const a


open Asymptotics


/- The Nevanlinna height functions `T_infty` of a meromorphic function `f` and
of `f - const` agree asymptotically, up to a constant. -/
theorem Nevanlinna_firstMain'₂ {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicOn f ⊤) :
    |(hf.T_infty) - ((hf.sub (MeromorphicOn.const a)).T_infty)| =O[Filter.atTop] (1 : ℝ → ℝ) := by
  rw [Asymptotics.isBigO_iff']
  use posLog ‖a‖ + log 2
  constructor
  · apply add_pos_of_nonneg_of_pos
    apply posLog_nonneg
    apply log_pos one_lt_two
  · rw [Filter.eventually_atTop]
    use 0
    intro b hb
    simp only [Pi.abs_apply, Pi.sub_apply, norm_eq_abs, abs_abs, Pi.one_apply,
      norm_one, mul_one]
    apply Nevanlinna_firstMain₂
