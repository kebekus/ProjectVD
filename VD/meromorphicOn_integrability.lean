import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.CircleIntegral
import VD.ToMathlib.Eliminate
import Mathlib.Analysis.Complex.CauchyIntegral


open Filter Interval MeasureTheory Metric Real Topology intervalIntegral

variable
  {ι : Type*}
  {E : Type*} [NormedAddCommGroup E]
  {μ : Measure ℝ}
  {a b R : ℝ}
  {c : ℂ}

/-- Finsums of interval integrable functions are interval integrable. -/
theorem IntervalIntegrable.finsum {f : ι → ℝ → E} (h : ∀ i, IntervalIntegrable (f i) μ a b) :
    IntervalIntegrable (∑ᶠ i, f i) μ a b := by
  by_cases h₁ : f.support.Finite
  · simp [finsum_eq_sum _ h₁, IntervalIntegrable.sum h₁.toFinset (fun i _ ↦ h i)]
  · rw [finsum_of_infinite_support h₁]
    apply intervalIntegrable_const_iff.2
    tauto

/--
If `f` is meromorphic over `ℝ`, then functions of the form `log ‖f ·‖` are
interval integrable.
-/
theorem MeromorphicOn.intervalIntegrable_log_norm [NormedSpace ℝ E] {f : ℝ → E}
    (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log ‖f ·‖) volume a b := by
  by_cases t₀ : ∀ u : [[a, b]], (hf u u.2).order ≠ ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((divisor f [[a, b]]).finiteSupport isCompact_uIcc)
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    rw [intervalIntegrable_congr_codiscreteWithin
      (h₄g.filter_mono (codiscreteWithin.mono Set.uIoc_subset_uIcc))]
    apply IntervalIntegrable.add
    · apply IntervalIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      rw [(by ring : a = ((a - i) + i)), (by ring : b = ((b - i) + i))]
      apply IntervalIntegrable.comp_sub_right (f := (log ‖·‖)) _ i
      simp [norm_eq_abs, log_abs]
    · apply ContinuousOn.intervalIntegrable
      apply h₁g.continuousOn.norm.log
      simp_all
  · rw [← hf.exists_order_ne_top_iff_forall (isConnected_Icc inf_le_sup)] at t₀
    push_neg at t₀
    have : (log ‖f ·‖) =ᶠ[codiscreteWithin (Ι a b)] 0 := by
      apply EventuallyEq.filter_mono _ (codiscreteWithin.mono Set.uIoc_subset_uIcc)
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        codiscreteWithin_self [[a, b]]] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.order_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    rw [intervalIntegrable_congr_codiscreteWithin this]
    apply _root_.intervalIntegrable_const_iff.2
    tauto

/--
If `f` is meromorphic over `ℝ`, then functions of the form `log ‖f⁺ ·‖` are
interval integrable.
-/
theorem MeromorphicOn.intervalIntegrable_posLog_norm [NormedSpace ℝ E] {f : ℝ → E}
    (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log⁺ ‖f ·‖) volume a b := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply IntervalIntegrable.add
  · apply hf.intervalIntegrable_log_norm.const_mul
  · apply hf.intervalIntegrable_log_norm.abs.const_mul

/--
If `f` is meromorphic over `ℝ`, then functions of the form `log ∘ f` are
interval integrable.
-/
theorem MeromorphicOn.intervalIntegrable_log {f : ℝ → ℝ}
    (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log ∘ f) volume a b := by
  rw [(by aesop : log ∘ f = (log ‖f ·‖))]
  exact hf.intervalIntegrable_log_norm

/-- Circle integrability is invariant when functions change along discrete sets. -/
theorem CircleIntegrable.congr_codiscreteWithin' {f₁ f₂ : ℂ → E} (hf₁ : CircleIntegrable f₁ c R)
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) :
    CircleIntegrable f₂ c R := by
  by_cases hR : R = 0
  · simp [hR]
  apply (intervalIntegrable_congr_codiscreteWithin _).1 hf₁
  rw [eventuallyEq_iff_exists_mem]
  exact ⟨(circleMap c R)⁻¹' {z | f₁ z = f₂ z},
    codiscreteWithin.mono (by simp only [Set.subset_univ]) (circleMap_preimage_codiscrete hR hf),
    by tauto⟩

/-- Sums of circle integrable functions are circle integrable. -/
theorem CircleIntegrable.sum (s : Finset ι) {f : ι → ℂ → E} (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    CircleIntegrable (∑ i ∈ s, f i) c R := by
  rw [CircleIntegrable,
    (by aesop : (fun θ ↦ (∑ i ∈ s, f i) (circleMap c R θ)) = ∑ i ∈ s, fun θ ↦ f i (circleMap c R θ))] at *
  exact IntervalIntegrable.sum s h

/-- Finsums of circle integrable functions are circle integrable. -/
theorem CircleIntegrable.finsum {f : ι → ℂ → E} (h : ∀ i, CircleIntegrable (f i) c R) :
    CircleIntegrable (∑ᶠ i, f i) c R := by
  by_cases h₁ : (Function.support f).Finite
  · rw [finsum_eq_sum f h₁]
    exact CircleIntegrable.sum h₁.toFinset (fun i _ ↦ h i)
  · rw [finsum_of_infinite_support h₁]
    apply circleIntegrable_const

theorem MeromorphicOn.circleIntegrable_log_norm [NormedSpace ℂ E] {f : ℂ → E}
    (hf : MeromorphicOn f (sphere c |R|)) :
    CircleIntegrable (log ‖f ·‖) c R := by
  by_cases t₀ : ∀ u : (sphere c |R|), (hf u u.2).order ≠ ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((divisor f (sphere c |R|)).finiteSupport (isCompact_sphere c |R|))
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    apply CircleIntegrable.congr_codiscreteWithin' _ h₄g.symm
    apply CircleIntegrable.add
    · apply CircleIntegrable.finsum
      intro i
      unfold CircleIntegrable
      apply IntervalIntegrable.const_mul
      apply MeromorphicOn.intervalIntegrable_log_norm
      apply AnalyticOnNhd.meromorphicOn
      apply AnalyticOnNhd.sub _ analyticOnNhd_const
      apply (analyticOnNhd_circleMap c R).mono (by tauto)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.log
      · apply ContinuousOn.norm
        apply h₁g.continuousOn.comp (t := sphere c |R|) (continuous_circleMap c R).continuousOn
        intro x hx
        simp
      · intro x hx
        rw [ne_eq, norm_eq_zero]
        apply h₂g ⟨circleMap c R x, circleMap_mem_sphere' c R x⟩
  · rw [← hf.exists_order_ne_top_iff_forall (isConnected_sphere (by simp) c (abs_nonneg R))] at t₀
    push_neg at t₀
    have : (log ‖f ·‖) =ᶠ[codiscreteWithin (sphere c |R|)] 0 := by
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        codiscreteWithin_self (sphere c |R|)] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.order_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    apply CircleIntegrable.congr_codiscreteWithin' (circleIntegrable_const 0 c R) this.symm

theorem MeromorphicOn.circleIntegrable_posLog_norm [NormedSpace ℂ E] {f : ℂ → E}
    (hf : MeromorphicOn f (sphere c |R|)) :
    CircleIntegrable (log⁺ ‖f ·‖) c R := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply CircleIntegrable.add
  · apply hf.circleIntegrable_log_norm.const_mul
  · apply IntervalIntegrable.const_mul
    apply hf.circleIntegrable_log_norm.abs

theorem analyticOnNhd_realPart {f : ℂ → ℂ} (h : AnalyticOnNhd ℂ f Set.univ) :
    AnalyticOnNhd ℝ (fun x ↦ (f x).re : ℝ → ℝ) Set.univ := by
  have : (fun x ↦ (f x).re : ℝ → ℝ) = Complex.reCLM ∘ f ∘ Complex.ofRealCLM := by
    ext x
    tauto
  rw [this]
  apply ContinuousLinearMap.comp_analyticOnNhd Complex.reCLM
  apply AnalyticOnNhd.comp'
  apply ((h.restrictScalars (𝕜' := ℂ)).mono (t := Set.univ))
  tauto
  exact Complex.ofRealCLM.analyticOnNhd Set.univ

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
  let A := (intervalIntegrable_log_sin (a := 0) (b := π / 2)).comp_sub_left (π / 2)
  simp only [Function.comp_apply, sub_zero, sub_self, sin_pi_div_two_sub] at A
  apply IntervalIntegrable.symm
  rwa [← (by rfl : (fun x => log (cos x)) = log ∘ cos)]
