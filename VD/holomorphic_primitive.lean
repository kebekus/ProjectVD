import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Data.ENNReal.Basic

noncomputable def primitive
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] :
  ℂ  → (ℂ → E) → (ℂ → E) := by
  intro z₀
  intro f
  exact fun z ↦ (∫ (x : ℝ) in z₀.re..z.re, f ⟨x, z₀.im⟩) + Complex.I • ∫ (x : ℝ) in z₀.im..z.im, f ⟨z.re, x⟩


theorem primitive_zeroAtBasepoint
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (f : ℂ  → E)
  (z₀ : ℂ) :
  (primitive z₀ f) z₀ = 0 := by
  unfold primitive
  simp


theorem primitive_fderivAtBasepointZero
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ  → E}
  {R : ℝ}
  (hR : 0 < R)
  (hf : ContinuousOn f (Metric.ball 0 R)) :
  HasDerivAt (primitive 0 f) (f 0) 0 := by
  unfold primitive
  simp
  apply hasDerivAt_iff_isLittleO.2
  simp
  rw [Asymptotics.isLittleO_iff]
  intro c hc

  have {z : ℂ} {e : E} : z • e = (∫ (_ : ℝ) in (0)..(z.re), e) + Complex.I • ∫ (_ : ℝ) in (0)..(z.im), e:= by
    simp
    rw [smul_comm]
    rw [← smul_assoc]
    simp
    have : z.re • e = (z.re : ℂ) • e := by exact rfl
    rw [this, ← add_smul]
    simp
  conv =>
    left
    intro x
    left
    arg 1
    arg 2
    rw [this]

  obtain ⟨s, h₁s, h₂s⟩ : ∃ s ⊆ f⁻¹' Metric.ball (f 0) (c / (4 : ℝ)), IsOpen s ∧ 0 ∈ s := by
    apply eventually_nhds_iff.mp
    apply continuousAt_def.1
    apply Continuous.continuousAt
    fun_prop

    apply continuousAt_def.1
    apply hf.continuousAt
    exact Metric.ball_mem_nhds 0 hR
    apply Metric.ball_mem_nhds (f 0)
    simpa

  obtain ⟨ε, h₁ε, h₂ε⟩ : ∃ ε > 0, (Metric.ball 0 ε) ×ℂ (Metric.ball 0 ε) ⊆ s ∧ (Metric.ball 0 ε) ×ℂ (Metric.ball 0 ε) ⊆ Metric.ball 0 R := by
    obtain ⟨ε', h₁ε', h₂ε'⟩ : ∃ ε' > 0, Metric.ball 0 ε' ⊆ s ∩ Metric.ball 0 R := by
      apply Metric.mem_nhds_iff.mp
      apply IsOpen.mem_nhds
      apply IsOpen.inter
      exact h₂s.1
      exact Metric.isOpen_ball
      constructor
      · exact h₂s.2
      · simpa

    use (2 : ℝ)⁻¹ * ε'

    constructor
    · simpa
    · constructor
      · intro x hx
        apply (h₂ε' _).1
        simp
        calc ‖x‖
        _ ≤ |x.re| + |x.im| := Complex.norm_le_abs_re_add_abs_im x
        _ < (2 : ℝ)⁻¹ * ε' + |x.im| := by
          apply (add_lt_add_iff_right |x.im|).mpr
          have : x.re ∈ Metric.ball 0 (2⁻¹ * ε') := (Complex.mem_reProdIm.1 hx).1
          simp at this
          exact this
        _ < (2 : ℝ)⁻¹ * ε' + (2 : ℝ)⁻¹ * ε' := by
          apply (add_lt_add_iff_left ((2 : ℝ)⁻¹ * ε')).mpr
          have : x.im ∈ Metric.ball 0 (2⁻¹ * ε') := (Complex.mem_reProdIm.1 hx).2
          simp at this
          exact this
        _ = ε' := by
          rw [← add_mul]
          abel_nf
          simp
      · intro x hx
        apply (h₂ε' _).2
        simp
        calc ‖x‖
        _ ≤ |x.re| + |x.im| := Complex.norm_le_abs_re_add_abs_im x
        _ < (2 : ℝ)⁻¹ * ε' + |x.im| := by
          apply (add_lt_add_iff_right |x.im|).mpr
          have : x.re ∈ Metric.ball 0 (2⁻¹ * ε') := (Complex.mem_reProdIm.1 hx).1
          simp at this
          exact this
        _ < (2 : ℝ)⁻¹ * ε' + (2 : ℝ)⁻¹ * ε' := by
          apply (add_lt_add_iff_left ((2 : ℝ)⁻¹ * ε')).mpr
          have : x.im ∈ Metric.ball 0 (2⁻¹ * ε') := (Complex.mem_reProdIm.1 hx).2
          simp at this
          exact this
        _ = ε' := by
          rw [← add_mul]
          abel_nf
          simp

  have h₃ε : ∀ y ∈ (Metric.ball 0 ε) ×ℂ (Metric.ball 0 ε), ‖(f y) - (f 0)‖ < (c / (4 : ℝ)) := by
    intro y hy
    apply mem_ball_iff_norm.mp
    apply h₁s
    exact h₂ε.1 hy


  have intervalComputation_uIcc {x' y' : ℝ} (h : x' ∈ Set.uIcc 0 y') : |x'| ≤ |y'| := by
    let A := h.1
    let B := h.2
    rcases le_total 0 y' with hy | hy
    · simp [hy] at A
      simp [hy] at B
      rwa [abs_of_nonneg A, abs_of_nonneg hy]
    · simp [hy] at A
      simp [hy] at B
      rw [abs_of_nonpos hy]
      rw [abs_of_nonpos]
      linarith [h.1]
      exact B


  rw [Filter.eventually_iff_exists_mem]
  use Metric.ball 0 (ε / (4 : ℝ))

  constructor
  · apply Metric.ball_mem_nhds 0
    linarith
  · intro y hy

    have {A B C D :E} : (A + B) - (C + D) = (A - C) + (B - D) := by
      abel
    rw [this]
    rw [← smul_sub]


    have t₀ : IntervalIntegrable (fun x => f { re := x, im := 0 }) MeasureTheory.volume 0 y.re := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.comp
      exact hf
      have : (fun x => ({ re := x, im := 0 } : ℂ)) = Complex.ofRealLI := by rfl
      rw [this]
      apply Continuous.continuousOn
      continuity
      intro x hx
      apply h₂ε.2
      simp
      constructor
      · simp
        calc |x|
        _ ≤ |y.re| := by apply intervalComputation_uIcc hx
        _ ≤ ‖y‖ := by exact Complex.abs_re_le_norm y
        _ < ε / 4 := by simp at hy; assumption
        _ < ε := by linarith
      · simpa
    have t₁ : IntervalIntegrable (fun _ => f 0) MeasureTheory.volume 0 y.re := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.comp
      apply hf
      fun_prop
      intro x _
      simpa
    rw [← intervalIntegral.integral_sub t₀ t₁]

    have t₂ : IntervalIntegrable (fun x_1 => f { re := y.re, im := x_1 }) MeasureTheory.volume 0 y.im := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.comp
      exact hf
      have : (Complex.mk y.re) = (fun x => Complex.I • Complex.ofRealCLM x + { re := y.re, im := 0 }) := by
        funext x
        apply Complex.ext
        rw [Complex.add_re]
        simp
        simp
      rw [this]
      apply ContinuousOn.add
      apply Continuous.continuousOn
      continuity
      fun_prop
      intro x hx
      apply h₂ε.2
      constructor
      · simp
        calc |y.re|
        _ ≤ ‖y‖ := by exact Complex.abs_re_le_norm y
        _ < ε / 4 := by simp at hy; assumption
        _ < ε := by linarith
      · simp
        calc |x|
        _ ≤ |y.im| := by apply intervalComputation_uIcc hx
        _ ≤ ‖y‖ := by exact Complex.abs_im_le_norm y
        _ < ε / 4 := by simp at hy; assumption
        _ < ε := by linarith
    have t₃ : IntervalIntegrable (fun _ => f 0) MeasureTheory.volume 0 y.im := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.comp
      exact hf
      fun_prop
      intro x _
      apply h₂ε.2
      simp
      constructor
      · simpa
      · simpa
    rw [← intervalIntegral.integral_sub t₂ t₃]

    have h₁y : |y.re| < ε / 4 := by
      calc |y.re|
      _ ≤ ‖y‖ := by apply Complex.abs_re_le_norm
      _ < ε / 4 := by
        let A := mem_ball_iff_norm.1 hy
        simp at A
        linarith
    have h₂y : |y.im| < ε / 4 := by
      calc |y.im|
      _ ≤ ‖y‖ := by apply Complex.abs_im_le_norm
      _ < ε / 4 := by
        let A := mem_ball_iff_norm.1 hy
        simp at A
        linarith

    have intervalComputation {x' y' : ℝ} (h : x' ∈ Ι 0 y') : |x'| ≤ |y'| := by
      let A := h.1
      let B := h.2
      rcases le_total 0 y' with hy | hy
      · simp [hy] at A
        simp [hy] at B
        rw [abs_of_nonneg hy]
        rw [abs_of_nonneg A.le]
        exact B
      · simp [hy] at A
        simp [hy] at B
        rw [abs_of_nonpos hy]
        rw [abs_of_nonpos]
        linarith [h.1]
        exact B

    have t₁ : ‖(∫ (x : ℝ) in (0)..(y.re), f { re := x, im := 0 } - f 0)‖ ≤ (c / (4 : ℝ)) * |y.re - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx

      have h₁x : |x| < ε / 4 := by
        calc |x|
          _ ≤ |y.re| := intervalComputation hx
          _ < ε / 4 := h₁y
      apply le_of_lt
      apply h₃ε { re := x, im := 0 }
      constructor
      · simp
        linarith
      · simp
        exact h₁ε

    have t₂ : ‖∫ (x : ℝ) in (0)..(y.im), f { re := y.re, im := x } - f 0‖ ≤ (c / (4 : ℝ)) * |y.im - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx

      have h₁x : |x| < ε / 4 := by
        calc |x|
          _ ≤ |y.im| := intervalComputation hx
          _ < ε / 4 := h₂y

      apply le_of_lt
      apply h₃ε { re := y.re, im := x }
      constructor
      · simp
        linarith
      · simp
        linarith

    calc ‖(∫ (x : ℝ) in (0)..(y.re), f { re := x, im := 0 } - f 0) + Complex.I • ∫ (x : ℝ) in (0)..(y.im), f { re := y.re, im := x } - f 0‖
      _ ≤ ‖(∫ (x : ℝ) in (0)..(y.re), f { re := x, im := 0 } - f 0)‖ + ‖Complex.I • ∫ (x : ℝ) in (0)..(y.im), f { re := y.re, im := x } - f 0‖ := by
        apply norm_add_le
      _ ≤ ‖(∫ (x : ℝ) in (0)..(y.re), f { re := x, im := 0 } - f 0)‖ + ‖∫ (x : ℝ) in (0)..(y.im), f { re := y.re, im := x } - f 0‖ := by
        simp
        rw [norm_smul]
        simp
      _ ≤ (c / (4 : ℝ)) * |y.re - 0| + (c / (4 : ℝ)) * |y.im - 0| := by
        apply add_le_add
        exact t₁
        exact t₂
      _ ≤ (c / (4 : ℝ)) * (|y.re| + |y.im|) := by
        simp
        rw [mul_add]
      _ ≤ (c / (4 : ℝ)) * (4 * ‖y‖) := by
        have : |y.re| + |y.im| ≤ 4 * ‖y‖ := by
          calc |y.re| + |y.im|
            _ ≤ ‖y‖ + ‖y‖ := by
              apply add_le_add
              apply Complex.abs_re_le_norm
              apply Complex.abs_im_le_norm
            _ ≤ 4 * ‖y‖ := by
              rw [← two_mul]
              apply mul_le_mul
              linarith
              rfl
              exact norm_nonneg y
              linarith

        apply mul_le_mul
        rfl
        exact this
        apply add_nonneg
        apply abs_nonneg
        apply abs_nonneg
        linarith
      _ ≤ c * ‖y‖ := by
        linarith


theorem primitive_translation
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (f : ℂ  → E)
  (z₀ t : ℂ) :
  primitive z₀ (f ∘ fun z ↦ (z - t)) = ((primitive (z₀ - t) f) ∘ fun z ↦ (z - t)) := by
  funext z
  unfold primitive
  simp

  let g : ℝ → E := fun x ↦ f ( {re := x, im := z₀.im - t.im} )
  have {x : ℝ} : f ({ re := x, im := z₀.im } - t) = g (1*x - t.re) := by
    congr 1
    apply Complex.ext <;> simp
  conv =>
    left
    left
    arg 1
    intro x
    rw [this]
  rw [intervalIntegral.integral_comp_mul_sub g one_ne_zero (t.re)]
  simp

  congr 1
  let g : ℝ → E := fun x ↦ f ( {re := z.re - t.re, im := x} )
  have {x : ℝ} : f ({ re := z.re, im := x} - t) = g (1*x - t.im) := by
    congr 1
    apply Complex.ext <;> simp
  conv =>
    left
    arg 2
    arg 1
    intro x
    rw [this]
  rw [intervalIntegral.integral_comp_mul_sub g one_ne_zero (t.im)]
  simp [g]



theorem primitive_hasDerivAtBasepoint
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ  → E}
  {R : ℝ}
  (z₀ : ℂ)
  (hR : 0 < R)
  (hf : ContinuousOn f (Metric.ball z₀ R)) :
  HasDerivAt (primitive z₀ f) (f z₀) z₀ := by

  let g := f ∘ fun z ↦ z + z₀
  have hg : ContinuousOn g (Metric.ball 0 R) := by
    apply ContinuousOn.comp
    fun_prop
    fun_prop
    intro x hx
    simp
    simp at hx
    assumption

  let B := primitive_translation g z₀ z₀
  simp at B
  have : (g ∘ fun z ↦ (z - z₀)) = f := by
    funext z
    dsimp [g]
    simp
  rw [this] at B
  rw [B]
  have : f z₀ = (1 : ℂ) • (f z₀) := (MulAction.one_smul (f z₀)).symm
  conv =>
    arg 2
    rw [this]

  apply HasDerivAt.scomp
  simp
  have : g 0 = f z₀ := by simp [g]
  rw [← this]
  exact primitive_fderivAtBasepointZero hR hg
  apply HasDerivAt.sub_const
  have : (fun (x : ℂ) ↦ x) = id := by
    funext x
    simp
  rw [this]
  exact hasDerivAt_id z₀



theorem primitive_additivity
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ  → E}
  {z₀ : ℂ}
  {rx ry : ℝ}
  (hf : DifferentiableOn ℂ f (Metric.ball z₀.re rx ×ℂ Metric.ball z₀.im ry))
  (hry : 0 < ry)
  {z₁ : ℂ}
  (hz₁ : z₁ ∈ (Metric.ball z₀.re rx ×ℂ Metric.ball z₀.im ry))
  :
  ∃ εx > 0, ∃ εy > 0, ∀ z ∈ (Metric.ball z₁.re εx ×ℂ Metric.ball z₁.im εy), (primitive z₀ f z) - (primitive z₁ f z) - (primitive z₀ f z₁) = 0 := by

  let εx := rx - dist z₀.re z₁.re
  have hεx : εx > 0 := by
    let A := hz₁.1
    simp at A
    dsimp [εx]
    rw [dist_comm]
    simpa
  let εy := ry - dist z₀.im z₁.im
  have hεy : εy > 0 := by
    let A := hz₁.2
    simp at A
    dsimp [εy]
    rw [dist_comm]
    simpa

  use εx
  use hεx
  use εy
  use hεy

  intro z hz

  unfold primitive

  have : (∫ (x : ℝ) in z₀.re..z.re, f { re := x, im := z₀.im }) = (∫ (x : ℝ) in z₀.re..z₁.re, f { re := x, im := z₀.im }) + (∫ (x : ℝ) in z₁.re..z.re, f { re := x, im := z₀.im }) := by

    rw [intervalIntegral.integral_add_adjacent_intervals]

    -- IntervalIntegrable (fun x => f { re := x, im := z₀.im }) MeasureTheory.volume z₀.re z₁.re
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp
    exact hf.continuousOn
    have {b : ℝ} : ((fun x => { re := x, im := b }) : ℝ → ℂ) = (fun x => Complex.ofRealCLM x + { re := 0, im := b }) := by
      funext x
      apply Complex.ext
      rw [Complex.add_re]
      simp
      rw [Complex.add_im]
      simp
    apply Continuous.continuousOn
    rw [this]
    continuity
    -- Remains: Set.MapsTo (fun x => { re := x, im := z₀.im }) (Set.uIcc z₀.re z₁.re) (Metric.ball z₀.re rx ×ℂ Metric.ball z₀.im ry)
    intro w hw
    simp
    apply Complex.mem_reProdIm.mpr
    constructor
    · simp
      calc dist w z₀.re
      _ ≤ dist z₁.re z₀.re := by apply Real.dist_right_le_of_mem_uIcc; rwa [Set.uIcc_comm] at hw
      _ < rx := by apply Metric.mem_ball.mp (Complex.mem_reProdIm.1 hz₁).1
    · simpa

    -- IntervalIntegrable (fun x => f { re := x, im := z₀.im }) MeasureTheory.volume z₁.re z.re
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp
    exact hf.continuousOn
    have {b : ℝ} : ((fun x => { re := x, im := b }) : ℝ → ℂ) = (fun x => Complex.ofRealCLM x + { re := 0, im := b }) := by
      funext x
      apply Complex.ext
      rw [Complex.add_re]
      simp
      rw [Complex.add_im]
      simp
    apply Continuous.continuousOn
    rw [this]
    continuity
    -- Remains: Set.MapsTo (fun x => { re := x, im := z₀.im }) (Set.uIcc z₁.re z.re) (Metric.ball z₀.re rx ×ℂ Metric.ball z₀.im ry)
    intro w hw
    simp
    constructor
    · simp
      calc dist w z₀.re
      _ ≤ dist w z₁.re + dist z₁.re z₀.re := by exact dist_triangle w z₁.re z₀.re
      _ ≤ dist z.re z₁.re + dist z₁.re z₀.re := by
        apply (add_le_add_iff_right (dist z₁.re z₀.re)).mpr
        rw [Set.uIcc_comm] at hw
        exact Real.dist_right_le_of_mem_uIcc hw
      _ < (rx - dist z₀.re z₁.re) + dist z₁.re z₀.re := by
        apply (add_lt_add_iff_right (dist z₁.re z₀.re)).mpr
        apply Metric.mem_ball.1 (Complex.mem_reProdIm.1 hz).1
      _ = rx := by
        rw [dist_comm]
        simp
    · simpa
  rw [this]

  have : (∫ (x : ℝ) in z₀.im..z.im, f { re := z.re, im := x }) = (∫ (x : ℝ) in z₀.im..z₁.im, f { re := z.re, im := x }) + (∫ (x : ℝ) in z₁.im..z.im, f { re := z.re, im := x }) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]

    -- IntervalIntegrable (fun x => f { re := z.re, im := x }) MeasureTheory.volume z₀.im z₁.im
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp
    exact hf.continuousOn
    apply Continuous.continuousOn
    have {b : ℝ}:  (Complex.mk b) = (fun x => Complex.I • Complex.ofRealCLM x + { re := b, im := 0 }) := by
      funext x
      apply Complex.ext
      rw [Complex.add_re]
      simp
      simp
    rw [this]
    apply Continuous.add
    fun_prop
    fun_prop
    -- Set.MapsTo (Complex.mk z.re) (Set.uIcc z₀.im z₁.im) (Metric.ball z₀.re rx ×ℂ Metric.ball z₀.im ry)
    intro w hw
    constructor
    · simp
      calc dist z.re z₀.re
      _ ≤ dist z.re z₁.re + dist z₁.re z₀.re := by exact dist_triangle z.re z₁.re z₀.re
      _ < (rx - dist z₀.re z₁.re) + dist z₁.re z₀.re := by
        apply (add_lt_add_iff_right (dist z₁.re z₀.re)).mpr
        apply Metric.mem_ball.1 (Complex.mem_reProdIm.1 hz).1
      _ = rx := by
        rw [dist_comm]
        simp
    · simp
      calc dist w z₀.im
      _ ≤ dist z₁.im z₀.im := by rw [Set.uIcc_comm] at hw; exact Real.dist_right_le_of_mem_uIcc hw
      _ < ry := by
        rw [← Metric.mem_ball]
        exact hz₁.2

    -- IntervalIntegrable (fun x => f { re := z.re, im := x }) MeasureTheory.volume z₁.im z.im
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp
    exact hf.continuousOn
    apply Continuous.continuousOn
    have {b : ℝ}:  (Complex.mk b) = (fun x => Complex.I • Complex.ofRealCLM x + { re := b, im := 0 }) := by
      funext x
      apply Complex.ext
      rw [Complex.add_re]
      simp
      simp
    rw [this]
    apply Continuous.add
    fun_prop
    fun_prop
    -- Set.MapsTo (Complex.mk z.re) (Set.uIcc z₁.im z.im) (Metric.ball z₀.re rx ×ℂ Metric.ball z₀.im ry)
    intro w hw
    constructor
    · simp
      calc dist z.re z₀.re
      _ ≤ dist z.re z₁.re + dist z₁.re z₀.re := by exact dist_triangle z.re z₁.re z₀.re
      _ < (rx - dist z₀.re z₁.re) + dist z₁.re z₀.re := by
        apply (add_lt_add_iff_right (dist z₁.re z₀.re)).mpr
        apply Metric.mem_ball.1 (Complex.mem_reProdIm.1 hz).1
      _ = rx := by
        rw [dist_comm]
        simp
    · simp
      calc dist w z₀.im
      _ ≤ dist w z₁.im + dist z₁.im z₀.im := by exact dist_triangle w z₁.im z₀.im
      _ ≤ dist z.im z₁.im + dist z₁.im z₀.im := by
        apply (add_le_add_iff_right (dist z₁.im z₀.im)).mpr
        rw [Set.uIcc_comm] at hw
        exact Real.dist_right_le_of_mem_uIcc hw
      _ < (ry - dist z₀.im z₁.im) + dist z₁.im z₀.im := by
        apply (add_lt_add_iff_right (dist z₁.im z₀.im)).mpr
        apply Metric.mem_ball.1 (Complex.mem_reProdIm.1 hz).2
      _ = ry := by
        rw [dist_comm]
        simp
  rw [this]

  simp

  have {a b c d e f g h : E} : (a + b) + (c + d) - (e + f) - (g + h) = b + (a - g) - e - f + d  - h + (c) := by
    abel
  rw [this]


  have H' : DifferentiableOn ℂ f (Set.uIcc z₁.re z.re ×ℂ Set.uIcc z₀.im z₁.im) := by
    apply DifferentiableOn.mono hf
    intro x hx
    constructor
    · simp
      calc dist x.re z₀.re
      _ ≤ dist x.re z₁.re + dist z₁.re z₀.re := by exact dist_triangle x.re z₁.re z₀.re
      _ ≤ dist z.re z₁.re + dist z₁.re z₀.re := by
        apply (add_le_add_iff_right (dist z₁.re z₀.re)).mpr
        rw [Set.uIcc_comm] at hx
        apply Real.dist_right_le_of_mem_uIcc (Complex.mem_reProdIm.1 hx).1
      _ < (rx - dist z₀.re z₁.re) + dist z₁.re z₀.re := by
        apply (add_lt_add_iff_right (dist z₁.re z₀.re)).mpr
        apply Metric.mem_ball.1 (Complex.mem_reProdIm.1 hz).1
      _ = rx := by
        rw [dist_comm]
        simp
    · simp
      calc dist x.im z₀.im
      _ ≤ dist z₀.im z₁.im := by rw [dist_comm]; exact Real.dist_left_le_of_mem_uIcc (Complex.mem_reProdIm.1 hx).2
      _ < ry := by
        rw [dist_comm]
        exact Metric.mem_ball.1 (Complex.mem_reProdIm.1 hz₁).2

  let A := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨z₁.re, z₀.im⟩ ⟨z.re, z₁.im⟩ H'
  have {x : ℝ} {w : ℂ} : ↑x + w.im * Complex.I = { re := x, im := w.im } := by
    apply Complex.ext
    · simp
    · simp
  simp_rw [this] at A
  have {x : ℝ} {w : ℂ} : w.re + x * Complex.I = { re := w.re, im := x } := by
    apply Complex.ext
    · simp
    · simp
  simp_rw [this] at A
  rw [← A]
  abel


theorem primitive_additivity'
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ  → E}
  {z₀ z₁ : ℂ}
  {R : ℝ}
  (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
  (hz₁ : z₁ ∈ Metric.ball z₀ R)
  :
  primitive z₀ f =ᶠ[nhds z₁] fun z ↦ (primitive z₁ f z) + (primitive z₀ f z₁) := by

  let d := fun ε ↦ √((dist z₁.re z₀.re + ε) ^ 2 + (dist z₁.im z₀.im + ε) ^ 2)
  have h₀d : Continuous d := by continuity
  have h₁d : ∀ ε, 0 ≤ d ε := fun ε ↦ Real.sqrt_nonneg ((dist z₁.re z₀.re + ε) ^ 2 + (dist z₁.im z₀.im + ε) ^ 2)

  obtain ⟨ε, h₀ε, h₁ε⟩ : ∃ ε > 0, d ε < R := by
    let Omega := d⁻¹' Metric.ball 0 R

    have lem₀Ω : IsOpen Omega := IsOpen.preimage h₀d Metric.isOpen_ball
    have lem₁Ω : 0 ∈ Omega := by
      dsimp [Omega, d]; simp
      have : dist z₁.re z₀.re = |z₁.re - z₀.re| := by exact rfl
      rw [this]
      have : dist z₁.im z₀.im = |z₁.im - z₀.im| := by exact rfl
      rw [this]
      simp
      rw [← Complex.dist_eq_re_im]; simp
      exact hz₁
    obtain ⟨ε, h₁ε, h₂ε⟩ := Metric.isOpen_iff.1 lem₀Ω 0 lem₁Ω

    let ε' := (2 : ℝ)⁻¹ * ε

    have h₀ε' : ε' ∈ Omega := by
      apply h₂ε
      dsimp [ε']; simp
      have : |ε| = ε := by apply abs_of_pos h₁ε
      rw [this]
      apply (inv_mul_lt_iff₀ zero_lt_two).mpr
      linarith
    have h₁ε' : 0 < ε' := by
      apply mul_pos _ h₁ε
      apply inv_pos.mpr
      exact zero_lt_two

    use ε'

    constructor
    · exact h₁ε'
    · dsimp [Omega] at h₀ε'; simp at h₀ε'
      rwa [abs_of_nonneg (h₁d ε')] at h₀ε'

  let rx := dist z₁.re z₀.re + ε
  let ry := dist z₁.im z₀.im + ε

  have h'ry : 0 < ry := by
    dsimp [ry]
    apply add_pos_of_nonneg_of_pos
    exact dist_nonneg
    simpa

  have h'f : DifferentiableOn ℂ f (Metric.ball z₀.re rx ×ℂ Metric.ball z₀.im ry) := by
    apply hf.mono
    intro x hx
    simp
    rw [Complex.dist_eq_re_im]

    have t₀ : dist x.re z₀.re < rx := Metric.mem_ball.mp hx.1
    have t₁ : dist x.im z₀.im < ry := Metric.mem_ball.mp hx.2
    have t₂ : √((x.re - z₀.re) ^ 2 + (x.im - z₀.im) ^ 2) < √( rx ^ 2 + ry ^ 2) := by
      rw [Real.sqrt_lt_sqrt_iff]
      apply add_lt_add
      · rw [sq_lt_sq]
        dsimp [dist] at t₀
        nth_rw 2 [abs_of_nonneg]
        assumption
        apply add_nonneg dist_nonneg h₀ε.le
      · rw [sq_lt_sq]
        dsimp [dist] at t₁
        nth_rw 2 [abs_of_nonneg]
        assumption
        apply add_nonneg dist_nonneg h₀ε.le
      apply add_nonneg
      exact sq_nonneg (x.re - z₀.re)
      exact sq_nonneg (x.im - z₀.im)

    calc √((x.re - z₀.re) ^ 2 + (x.im - z₀.im) ^ 2)
    _ < √( rx ^ 2 + ry ^ 2) := by
      exact t₂
    _ = d ε := by dsimp [d, rx, ry]
    _ < R := by exact h₁ε

  have h'z₁ : z₁ ∈ (Metric.ball z₀.re rx ×ℂ Metric.ball z₀.im ry) := by
    dsimp [rx, ry]
    constructor
    · simp; exact h₀ε
    · simp; exact h₀ε

  obtain ⟨εx, hεx, εy, hεy, hε⟩ := primitive_additivity h'f h'ry h'z₁

  apply Filter.eventuallyEq_iff_exists_mem.2
  use (Metric.ball z₁.re εx ×ℂ Metric.ball z₁.im εy)
  constructor
  · apply IsOpen.mem_nhds
    apply IsOpen.reProdIm
    exact Metric.isOpen_ball
    exact Metric.isOpen_ball
    constructor
    · simpa
    · simpa
  · intro x hx
    simp
    rw [← sub_zero (primitive z₀ f x), ← hε x hx]
    abel


theorem primitive_hasDerivAt
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ  → E}
  {z₀ z : ℂ}
  {R : ℝ}
  (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
  (hz : z ∈ Metric.ball z₀ R) :
  HasDerivAt (primitive z₀ f) (f z) z := by

  let A := primitive_additivity' hf hz
  rw [Filter.EventuallyEq.hasDerivAt_iff A]
  rw [← add_zero (f z)]
  apply HasDerivAt.add

  let R' := R - dist z z₀
  have h₀R' : 0 < R' := by
    dsimp [R']
    simp
    exact hz
  have h₁R' : Metric.ball z R' ⊆ Metric.ball z₀ R := by
    intro x hx
    simp
    calc dist x z₀
    _ ≤ dist x z + dist z z₀ := dist_triangle x z z₀
    _ < R' + dist z z₀ := by
      refine add_lt_add_right ?bc (dist z z₀)
      exact hx
    _ = R := by
      dsimp [R']
      simp

  apply primitive_hasDerivAtBasepoint
  exact h₀R'
  apply ContinuousOn.mono hf.continuousOn h₁R'
  apply hasDerivAt_const


theorem primitive_differentiableOn
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ  → E}
  {z₀ : ℂ}
  {R : ℝ}
  (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
  :
  DifferentiableOn ℂ (primitive z₀ f) (Metric.ball z₀ R) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  exact (primitive_hasDerivAt hf hz).differentiableAt


theorem primitive_hasFderivAt
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ  → E}
  (z₀ : ℂ)
  (R : ℝ)
  (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
  :
  ∀ z ∈ Metric.ball z₀ R, HasFDerivAt (primitive z₀ f) ((ContinuousLinearMap.lsmul ℂ ℂ).flip (f z)) z := by
  intro z hz
  rw [hasFDerivAt_iff_hasDerivAt]
  simp
  apply primitive_hasDerivAt hf hz


theorem primitive_hasFderivAt'
  {f : ℂ  → ℂ}
  {z₀ : ℂ}
  {R : ℝ}
  (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
  :
  ∀ z ∈ Metric.ball z₀ R, HasFDerivAt (primitive z₀ f) (ContinuousLinearMap.lsmul ℂ ℂ (f z)) z := by
  intro z hz
  rw [hasFDerivAt_iff_hasDerivAt]
  simp
  exact primitive_hasDerivAt hf hz


theorem primitive_fderiv
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ  → E}
  {z₀ : ℂ}
  {R : ℝ}
  (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
  :
  ∀ z ∈ Metric.ball z₀ R, (fderiv ℂ (primitive z₀ f) z) = (ContinuousLinearMap.lsmul ℂ ℂ).flip (f z) := by
  intro z hz
  apply HasFDerivAt.fderiv
  exact primitive_hasFderivAt z₀ R hf z hz


theorem primitive_fderiv'
  {f : ℂ  → ℂ}
  {z₀ : ℂ}
  {R : ℝ}
  (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
  :
  ∀ z ∈ Metric.ball z₀ R, (fderiv ℂ (primitive z₀ f) z) = ContinuousLinearMap.lsmul ℂ ℂ (f z) := by
  intro z hz
  apply HasFDerivAt.fderiv
  exact primitive_hasFderivAt' hf z hz
