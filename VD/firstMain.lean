import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Integral.CircleIntegral
import VD.ToMathlib.divisor
import VD.meromorphicOn_divisor
import VD.meromorphicOn_integrability
import VD.stronglyMeromorphicOn
import VD.stronglyMeromorphic_JensenFormula

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

noncomputable def MeromorphicOn.N_zero
  {f : ℂ → ℂ}
  (hf : MeromorphicOn f ⊤) :
  ℝ → ℝ :=
  fun r ↦ ∑ᶠ z, (max 0 ((hf.restrict |r|).divisor z)) * log (r * ‖z‖⁻¹)
  --hf.divisor⁺.logCounting

noncomputable def MeromorphicOn.N_infty
  {f : ℂ → ℂ}
  (hf : MeromorphicOn f ⊤) :
  ℝ → ℝ :=
  fun r ↦ ∑ᶠ z, (max 0 (-((hf.restrict |r|).divisor z))) * log (r * ‖z‖⁻¹)


theorem Nevanlinna_counting₁₁
  {f : ℂ → ℂ}
  (hf : MeromorphicOn f ⊤)
  (a : ℂ) :
  (hf.add (MeromorphicOn.const a)).N_infty = hf.N_infty := by

  funext r
  unfold MeromorphicOn.N_infty
  let A := (hf.restrict |r|).divisor.finiteSupport (isCompact_closedBall 0 |r|)
  repeat
    rw [finsum_eq_sum_of_support_subset (s := A.toFinset)]
  apply Finset.sum_congr rfl
  intro x hx; simp at hx
  congr 2

  by_cases h : 0 ≤ (hf.restrict |r|).divisor x
  · simp [h]
    let A := (hf.restrict |r|).divisor_add_const₁ a h
    exact A

  · simp at h
    have h' : 0 ≤ -((hf.restrict |r|).divisor x) := by
      apply Int.le_neg_of_le_neg
      simp
      exact h.le
    simp [h']
    clear h'

    have A := (hf.restrict |r|).divisor_add_const₂ a h
    have A' : 0 ≤ -((MeromorphicOn.add (MeromorphicOn.restrict hf |r|) (MeromorphicOn.const a)).divisor x) := by
      apply Int.le_neg_of_le_neg
      simp
      exact A.le
    simp [A']
    clear A A'

    exact (hf.restrict |r|).divisor_add_const₃ a h
  --
  intro x
  contrapose
  simp
  intro hx
  rw [hx]
  tauto
  --
  intro x
  contrapose
  simp
  intro hx
  have : 0 ≤ (hf.restrict |r|).divisor x := by
    rw [hx]
  have G := (hf.restrict |r|).divisor_add_const₁ a this
  clear this
  simp [G]

theorem Nevanlinna_counting'₁₁
  {f : ℂ → ℂ}
  (hf : MeromorphicOn f ⊤)
  (a : ℂ) :
  (hf.sub (MeromorphicOn.const a)).N_infty = hf.N_infty := by
  have : (f - fun x => a) = (f + fun x => -a) := by
    funext x
    simp; ring
  have : (hf.sub (MeromorphicOn.const a)).N_infty = (hf.add (MeromorphicOn.const (-a))).N_infty := by
    simp
  rw [this]
  exact Nevanlinna_counting₁₁ hf (-a)

theorem Nevanlinna_counting₀
  {f : ℂ → ℂ}
  (hf : MeromorphicOn f ⊤) :
  hf.inv.N_infty = hf.N_zero := by

  funext r
  unfold MeromorphicOn.N_zero MeromorphicOn.N_infty
  let A := (hf.restrict |r|).divisor.finiteSupport (isCompact_closedBall 0 |r|)
  repeat
    rw [finsum_eq_sum_of_support_subset (s := A.toFinset)]
  apply Finset.sum_congr rfl
  intro x hx
  congr
  let B := hf.restrict_inv |r|
  rw [MeromorphicOn.divisor_inv]
  simp
  --
  exact fun x a => hf x trivial
  --
  intro x
  contrapose
  simp
  intro hx
  rw [hx]
  tauto
  --
  intro x
  contrapose
  simp
  intro hx h₁x

  rw [MeromorphicOn.divisor_inv (hf.restrict |r|)] at h₁x
  simp at h₁x
  rw [hx] at h₁x
  tauto

theorem Nevanlinna_counting
  {f : ℂ → ℂ}
  (hf : MeromorphicOn f ⊤) :
  hf.N_zero - hf.N_infty = fun r ↦ ∑ᶠ z, ((hf.restrict |r|).divisor z) * log (r * ‖z‖⁻¹) := by

  funext r
  simp only [Pi.sub_apply]
  unfold  MeromorphicOn.N_zero MeromorphicOn.N_infty

  let A := (hf.restrict |r|).divisor.finiteSupport (isCompact_closedBall 0 |r|)
  repeat
    rw [finsum_eq_sum_of_support_subset (s := A.toFinset)]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  congr
  funext x
  congr
  by_cases h : 0 ≤ (hf.restrict |r|).divisor x
  · simp [h]
  · have h' : 0 ≤ -((hf.restrict |r|).divisor x) := by
      simp at h
      apply Int.le_neg_of_le_neg
      simp
      exact h.le
    simp at h
    simp [h']
    linarith
  --
  repeat
    intro x
    contrapose
    simp
    intro hx
    rw [hx]
    tauto


--

noncomputable def MeromorphicOn.m_infty
  {f : ℂ → ℂ}
  (_ : MeromorphicOn f ⊤) :
  ℝ → ℝ :=
  fun r ↦ (2 * π)⁻¹ * ∫ x in (0)..(2 * π), posLog ‖f (circleMap 0 r x)‖


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
  apply MeromorphicOn.integrable_poslog_abs_f
  intro z hx
  exact h₁f z trivial
  --
  apply MeromorphicOn.integrable_poslog_abs_f
  exact MeromorphicOn.inv_iff.mpr fun x a => h₁f x trivial


noncomputable def MeromorphicOn.T_infty
  {f : ℂ → ℂ}
  (hf : MeromorphicOn f ⊤) :
  ℝ → ℝ :=
  hf.m_infty + hf.N_infty


theorem Nevanlinna_firstMain₁
  {f : ℂ → ℂ}
  (h₁f : MeromorphicOn f ⊤)
  (h₂f : MeromorphicNFAt f 0)
  (h₃f : f 0 ≠ 0) :
  (fun _ ↦ log ‖f 0‖) + h₁f.inv.T_infty = h₁f.T_infty := by

  rw [add_eq_of_eq_sub]
  unfold MeromorphicOn.T_infty

  have {A B C D : ℝ → ℝ} : A + B - (C + D) = A - C - (D - B) := by
    ring
  rw [this]
  clear this

  rw [Nevanlinna_counting₀ h₁f]
  rw [Nevanlinna_counting h₁f]
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
    rw [Nevanlinna_counting'₁₁ h₁f a]
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
  apply MeromorphicOn.integrable_poslog_abs_f
  exact fun x a => h₁f x trivial
  --
  apply MeromorphicOn.integrable_poslog_abs_f
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
