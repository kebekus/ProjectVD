import VD.specialFunctions_CircleIntegral_affine
import VD.stronglyMeromorphicOn_eliminate

open Real

theorem jensen₀
  {R : ℝ}
  (hR : 0 < R)
  (f : ℂ → ℂ)
  -- WARNING: Not needed. MeromorphicOn suffices
  (h₁f : StronglyMeromorphicOn f (Metric.closedBall 0 R))
  (h₂f : f 0 ≠ 0) :
  log ‖f 0‖ = -∑ᶠ s, (h₁f.meromorphicOn.divisor s) * log (R * ‖s‖⁻¹) + (2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖f (circleMap 0 R x)‖ := by

  have h₁U : IsConnected (Metric.closedBall (0 : ℂ) R) := by
    constructor
    · exact Metric.nonempty_closedBall.mpr hR.le
    · exact (convex_closedBall (0 : ℂ) R).isPreconnected

  have h₂U : IsCompact (Metric.closedBall (0 : ℂ) R) :=
    isCompact_closedBall 0 R

  have h'₂f : ∃ u : (Metric.closedBall (0 : ℂ) R), f u ≠ 0 := by
    use ⟨0, Metric.mem_closedBall_self hR.le⟩

  have h'₁f : MeromorphicNFAt f 0 := by
    apply h₁f
    simpa using hR.le

  have h''₂f : h'₁f.meromorphicAt.order = 0 := by
    rwa [h'₁f.order_eq_zero_iff]

  have h'''₂f : h₁f.meromorphicOn.divisor 0 = 0 := by
    unfold MeromorphicOn.divisor
    simp
    tauto

  have h₃f : Set.Finite (Function.support h₁f.meromorphicOn.divisor) := by
    exact (StronglyMeromorphicOn.meromorphicOn h₁f).divisor.finiteSupport h₂U

  have h'₃f : ∀ s ∈ h₃f.toFinset, s ≠ 0 := by
    by_contra hCon
    push_neg at hCon
    obtain ⟨s, h₁s, h₂s⟩ := hCon
    rw [h₂s] at h₁s
    simp at h₁s
    tauto

  have h₄f: Function.support (fun s ↦ (h₁f.meromorphicOn.divisor s) * log (R * ‖s‖⁻¹)) ⊆ h₃f.toFinset := by
    intro x
    contrapose
    simp
    intro hx
    rw [hx]
    simp
  rw [finsum_eq_sum_of_support_subset _ h₄f]

  obtain ⟨F, h₁F, h₂F, h₃F, h₄F⟩ := MeromorphicOn.decompose₃' h₂U h₁U h₁f h'₂f

  have h₁F : Function.mulSupport (fun u ↦ fun z => (z - u) ^ (h₁f.meromorphicOn.divisor u)) ⊆ h₃f.toFinset := by
    intro u
    contrapose
    simp
    intro hu
    rw [hu]
    simp
    exact rfl
  rw [finprod_eq_prod_of_mulSupport_subset _ h₁F] at h₄F

  let G := fun z ↦ log ‖F z‖ + ∑ᶠ s, (h₁f.meromorphicOn.divisor s) * log ‖z - s‖

  have h₁G {z : ℂ} : Function.support (fun s ↦ (h₁f.meromorphicOn.divisor s) * log ‖z - s‖) ⊆ h₃f.toFinset := by
    intro s
    contrapose
    simp
    intro hs
    rw [hs]
    simp

  have decompose_f : ∀ z ∈ Metric.closedBall (0 : ℂ) R, f z ≠ 0 → log ‖f z‖ = G z := by
    intro z h₁z h₂z

    rw [h₄F]
    simp only [Pi.mul_apply, norm_mul]
    simp only [Finset.prod_apply, norm_prod, norm_zpow]
    rw [Real.log_mul]
    rw [Real.log_prod]
    simp_rw [Real.log_zpow]
    dsimp only [G]
    rw [finsum_eq_sum_of_support_subset _ h₁G]
    --
    intro x hx
    have : z ≠ x := by
      by_contra hCon
      rw [← hCon] at hx
      simp at hx
      rw [← (h₁f z h₁z).order_eq_zero_iff] at h₂z
      unfold MeromorphicOn.divisor at hx
      simp [h₁z] at hx
      tauto
    apply zpow_ne_zero
    simp
    rwa [sub_eq_zero]
    -- Complex.abs (F z) ≠ 0
    simp
    exact h₃F ⟨z, h₁z⟩
    --
    rw [Finset.prod_ne_zero_iff]
    intro x hx
    have : z ≠ x := by
      by_contra hCon
      rw [← hCon] at hx
      simp at hx
      rw [← (h₁f z h₁z).order_eq_zero_iff] at h₂z
      unfold MeromorphicOn.divisor at hx
      simp [h₁z] at hx
      tauto
    apply zpow_ne_zero
    simp
    rwa [sub_eq_zero]


  have int_logAbs_f_eq_int_G : ∫ (x : ℝ) in (0)..2 * π, log ‖f (circleMap 0 R x)‖ = ∫ (x : ℝ) in (0)..2 * π, G (circleMap 0 R x) := by

    rw [intervalIntegral.integral_congr_ae]
    rw [MeasureTheory.ae_iff]
    apply Set.Countable.measure_zero
    simp

    have t₀ : {a | a ∈ Ι 0 (2 * π) ∧ ¬log ‖f (circleMap 0 R a)‖ = G (circleMap 0 R a)}
      ⊆ (circleMap 0 R)⁻¹' (h₃f.toFinset) := by
      intro a ha
      simp at ha
      simp
      by_contra C
      have t₀ : (circleMap 0 R a) ∈ Metric.closedBall 0 R := by
        apply circleMap_mem_closedBall
        exact hR.le
      have t₁ : f (circleMap 0 R a) ≠ 0 := by
        let A := h₁f (circleMap 0 R a) t₀
        rw [← A.order_eq_zero_iff]
        unfold MeromorphicOn.divisor at C
        simp [t₀] at C
        rcases C with C₁|C₂
        · assumption
        · let B := h₁f.meromorphicOn.exists_order_ne_top_iff_forall h₁U
          let C := fun q ↦ B.1 q ⟨(circleMap 0 R a), t₀⟩
          rw [C₂] at C
          have : ∃ u : (Metric.closedBall (0 : ℂ) R), (h₁f u u.2).meromorphicAt.order ≠ ⊤ := by
            use ⟨(0 : ℂ), (by simp; exact hR.le)⟩
            let H := h₁f 0 (by simp; exact hR.le)
            let K := H.order_eq_zero_iff.2 h₂f
            rw [K]
            simp
          let D := C this
          tauto
      exact ha.2 (decompose_f (circleMap 0 R a) t₀ t₁)

    apply Set.Countable.mono t₀
    apply Set.Countable.preimage_circleMap
    apply Set.Finite.countable
    exact Finset.finite_toSet h₃f.toFinset
    --
    exact hR.ne.symm


  have decompose_int_G : ∫ (x : ℝ) in (0)..2 * π, G (circleMap 0 R x)
    = (∫ (x : ℝ) in (0)..2 * π, log (norm (F (circleMap 0 R x))))
        + ∑ᶠ x, (h₁f.meromorphicOn.divisor x) * ∫ (x_1 : ℝ) in (0)..2 * π, log (norm (circleMap 0 R x_1 - ↑x)) := by
    dsimp [G]

    rw [intervalIntegral.integral_add]
    congr
    have t₀ {x : ℝ} : Function.support (fun s ↦ (h₁f.meromorphicOn.divisor s) * log (norm (circleMap 0 R x - s))) ⊆ h₃f.toFinset := by
      intro s hs
      simp at hs
      simp [hs.1]
    conv =>
      left
      arg 1
      intro x
      rw [finsum_eq_sum_of_support_subset _ t₀]
    rw [intervalIntegral.integral_finset_sum]
    let G' := fun x ↦ ((h₁f.meromorphicOn.divisor x) : ℂ) * ∫ (x_1 : ℝ) in (0)..2 * π, log (norm (circleMap 0 R x_1 - x))
    have t₁ : (Function.support fun x ↦ (h₁f.meromorphicOn.divisor x) * ∫ (x_1 : ℝ) in (0)..2 * π, log (norm (circleMap 0 R x_1 - x))) ⊆ h₃f.toFinset := by
      simp
      intro s
      contrapose!
      simp
      tauto
    conv =>
      right
      rw [finsum_eq_sum_of_support_subset _ t₁]
    simp

    --  ∀ i ∈ (finiteZeros h₁U h₂U h'₁f h'₂f).toFinset,
    --  IntervalIntegrable (fun x => (h'₁f.order i).toNat *
    --    log (Complex.abs (circleMap 0 1 x - ↑i))) MeasureTheory.volume 0 (2 * π)
    intro i _
    apply IntervalIntegrable.const_mul
    apply intervalIntegrable_logAbs_circleMap_sub_const
    linarith
    --
    -- case neg
    apply Continuous.intervalIntegrable
    apply continuous_iff_continuousAt.2
    intro x
    have : (fun x => log (norm ( F (circleMap 0 R x)))) = log ∘ norm ∘ F ∘ circleMap 0 R :=
      rfl
    rw [this]
    apply ContinuousAt.comp
    apply Real.continuousAt_log
    simp
    let A := h₃F ⟨(circleMap 0 R x), circleMap_mem_closedBall 0 hR.le x⟩
    exact A
    --
    apply ContinuousAt.comp
    apply continuous_norm.continuousAt
    apply ContinuousAt.comp
    let A := h₂F (circleMap 0 R x) (circleMap_mem_closedBall 0 hR.le x)
    apply A.continuousAt
    exact (continuous_circleMap 0 R).continuousAt
    -- IntervalIntegrable (fun x => ∑ᶠ (s : ℂ), ↑(↑⋯.divisor s) * log (Complex.abs (circleMap 0 1 x - s))) MeasureTheory.volume 0 (2 * π)
    --simp? at h₁G
    have h₁G' {z : ℂ} : (Function.support fun s => (h₁f.meromorphicOn.divisor s) * log (norm (z - s))) ⊆ ↑h₃f.toFinset := by
      exact h₁G
    conv =>
      arg 1
      intro z
      rw [finsum_eq_sum_of_support_subset _ h₁G']
    conv =>
      arg 1
      rw [← Finset.sum_fn]
    apply IntervalIntegrable.sum
    intro i _
    apply IntervalIntegrable.const_mul
    --have : i.1 ∈ Metric.closedBall (0 : ℂ) 1 := i.2
    --simp at this
    by_cases h₂i : ‖i‖ = R
    -- case pos
    --exact int'₂ h₂i
    apply intervalIntegrable_logAbs_circleMap_sub_const hR.ne.symm
    -- case neg
    apply Continuous.intervalIntegrable
    apply continuous_iff_continuousAt.2
    intro x
    have : (fun x => log (norm (circleMap 0 R x - ↑i))) = log ∘ norm ∘ (fun x ↦ circleMap 0 R x - ↑i) :=
      rfl
    rw [this]
    apply ContinuousAt.comp
    apply Real.continuousAt_log
    simp

    by_contra ha'
    rw [sub_eq_zero] at ha'
    conv at h₂i =>
      arg 1
      rw [← ha']
      rw [norm_circleMap_zero R x]
      simp
    linarith
    apply ContinuousAt.comp
    apply continuous_norm.continuousAt
    fun_prop

  have t₁ : (∫ (x : ℝ) in (0)..2 * Real.pi, log ‖F (circleMap 0 R x)‖) = 2 * Real.pi * log ‖F 0‖ := by
    let logAbsF := fun w ↦ Real.log ‖F w‖
    have t₀ : ∀ z ∈ Metric.closedBall 0 R, HarmonicAt logAbsF z := by
      intro z hz
      apply logabs_of_holomorphicAt_is_harmonic
      exact AnalyticAt.holomorphicAt (h₂F z hz)
      exact h₃F ⟨z, hz⟩

    apply harmonic_meanValue₁ R hR t₀


  rw [t₁] at decompose_int_G


  have h₁G' : (Function.support fun s => (h₁f.meromorphicOn.divisor s) * ∫ (x_1 : ℝ) in (0)..(2 * π), log ‖circleMap 0 R x_1 - s‖) ⊆ ↑h₃f.toFinset := by
    intro s hs
    simp at hs
    simp [hs.1]
  rw [finsum_eq_sum_of_support_subset _ h₁G'] at decompose_int_G
  have : ∑ s ∈ h₃f.toFinset, (h₁f.meromorphicOn.divisor s) * ∫ (x_1 : ℝ) in (0)..(2 * π), log ‖circleMap 0 R x_1 - s‖ = ∑ s ∈ h₃f.toFinset, (h₁f.meromorphicOn.divisor s) * (2 * π) * log R := by
    apply Finset.sum_congr rfl
    intro s hs
    have : s ∈ Metric.closedBall 0 R := by
      let A := h₁f.meromorphicOn.divisor.supportWithinDomain
      have : s ∈ Function.support h₁f.meromorphicOn.divisor := by
        simp at hs
        exact hs
      exact A this
    rw [int₄ hR this]
    linarith
  rw [this] at decompose_int_G


  --simp at decompose_int_G

  rw [int_logAbs_f_eq_int_G]
  rw [decompose_int_G]
  let X := h₄F
  nth_rw 1 [h₄F]
  simp
  have : π⁻¹ * 2⁻¹ * (2 * π) = 1 := by
    calc π⁻¹ * 2⁻¹ * (2 * π)
    _ = π⁻¹ * (2⁻¹ * 2) * π := by ring
    _ = π⁻¹ * π := by ring
    _ = (π⁻¹ * π) := by ring
    _ = 1 := by
      rw [inv_mul_cancel₀]
      exact pi_ne_zero
  --rw [this]
  rw [log_mul]
  rw [log_prod]
  simp
  rw [add_comm]
  rw [mul_add]
  rw [← mul_assoc (π⁻¹ * 2⁻¹), this]
  simp
  rw [add_comm]
  nth_rw 2 [add_comm]
  rw [add_assoc]
  congr
  rw [Finset.mul_sum]
  rw [← sub_eq_add_neg]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl]
  intro s hs
  rw [log_mul, log_inv]
  rw [← mul_assoc (π⁻¹ * 2⁻¹)]
  rw [mul_comm _ (2 * π)]
  rw [← mul_assoc (π⁻¹ * 2⁻¹)]
  rw [this]
  simp
  rw [mul_add]
  ring
  --
  exact hR.ne.symm
  --
  simp
  by_contra hCon
  rw [hCon] at hs
  simp at hs
  exact hs h'''₂f
  --
  intro s hs
  apply zpow_ne_zero
  simp
  by_contra hCon
  rw [hCon] at hs
  simp at hs
  exact hs h'''₂f
  --
  simp only [ne_eq, map_eq_zero]
  rw [← ne_eq]
  simp
  exact h₃F ⟨0, (by simp; exact hR.le)⟩
  --
  rw [Finset.prod_ne_zero_iff]
  intro s hs
  apply zpow_ne_zero
  simp
  by_contra hCon
  rw [hCon] at hs
  simp at hs
  exact hs h'''₂f


theorem jensen
  {R : ℝ}
  (hR : 0 < R)
  (f : ℂ → ℂ)
  (h₁f : MeromorphicOn f (Metric.closedBall 0 R))
  (h₁f' : MeromorphicNFAt f 0)
  (h₂f : f 0 ≠ 0) :
  log ‖f 0‖ = -∑ᶠ s, (h₁f.divisor s) * log (R * ‖s‖⁻¹) + (2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖f (circleMap 0 R x)‖ := by

  let F := h₁f.makeStronglyMeromorphicOn

  have : F 0 = f 0 := by
    unfold F
    have : 0 ∈ (Metric.closedBall 0 R) := by
      simp [hR.le]
    unfold MeromorphicOn.makeStronglyMeromorphicOn
    simp [this]
    intro h₁R

    let A := MeromorphicNFAt.toNF_eq_id h₁f'
    simp_rw [A]
  rw [← this]
  rw [← this] at h₂f
  clear this

  have h₁F := stronglyMeromorphicOn_of_makeStronglyMeromorphicOn h₁f

  rw [jensen₀ hR F h₁F h₂f]

  rw [h₁f.divisor_of_makeStronglyMeromorphicOn]
  congr 2
  have {x : ℝ} : log ‖F (circleMap 0 R x)‖ = (fun z ↦ log ‖F z‖) (circleMap 0 R x) := by
    rfl
  conv =>
    left
    arg 1
    intro x
    rw [this]
  have {x : ℝ} : log ‖f (circleMap 0 R x)‖ = (fun z ↦ log ‖f z‖) (circleMap 0 R x) := by
    rfl
  conv =>
    right
    arg 1
    intro x
    rw [this]

  have h'R : R ≠ 0 := hR.ne.symm
  have hU : Metric.sphere (0 : ℂ) |R| ⊆ (Metric.closedBall (0 : ℂ) R) := by
    have : R = |R| := by exact Eq.symm (abs_of_pos hR)
    nth_rw 2 [this]
    exact Metric.sphere_subset_closedBall

  let A := integral_congr_changeDiscrete h'R hU (f₁ := fun z ↦ log ‖F z‖) (f₂ := fun z ↦ log ‖f z‖)
  apply A
  clear A

  rw [Filter.eventuallyEq_iff_exists_mem]
  have A := makeStronglyMeromorphicOn_changeDiscrete'' h₁f
  rw [Filter.eventuallyEq_iff_exists_mem] at A
  obtain ⟨s, h₁s, h₂s⟩ := A
  use s
  constructor
  · exact h₁s
  · intro x hx
    let A := h₂s hx
    simp
    rw [A]
