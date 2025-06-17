import Mathlib.Analysis.Calculus.FDeriv.Congr
import VD.Harmonic

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedSpace ℂ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : ℂ → F}
  {s t : Set E} {c : ℝ}

open Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem y {f : E → F} {n : ℕ} {z : E} (h : ContDiffAt ℂ n f z) :
    (fun x : E ↦ ((iteratedFDeriv ℂ n f x).restrictScalars ℝ)) =ᶠ[𝓝 z]
      (fun x : E ↦ iteratedFDeriv ℝ n f x) := by
  induction n with
  | zero =>
    filter_upwards with a
    ext m
    simp [iteratedFDeriv_zero_apply m]
  | succ n hn =>
    have : ContDiffAt ℂ n f z := by
      apply h.of_le
      apply Nat.cast_le.mpr
      exact Nat.le_add_right n 1
    have t₀ := hn this
    have t₁ := this.eventually
    simp at t₁
    filter_upwards [t₀.eventually_nhds, t₁.eventually_nhds] with a h₁a h₂a
    ext m
    simp [iteratedFDeriv_succ_apply_left]

    have : (fun x ↦ (iteratedFDeriv ℂ n f x).restrictScalars ℝ) =ᶠ[𝓝 a] (fun x ↦ iteratedFDeriv ℝ n f x) := h₁a
    have := (this.fderiv (𝕜 := ℝ)).eq_of_nhds
    rw [← this]
    have s₀ : DifferentiableAt ℂ (iteratedFDeriv ℂ n f) a := by
      sorry
    have := s₀.fderiv_restrictScalars ℝ
    simp_all
    sorry


  sorry

theorem xx (h : ContDiffAt ℂ 2 f x) :
    HarmonicAt f x := by
  constructor
  · exact ContDiffAt.restrict_scalars ℝ h
  · have : Δ f x = 0 := by
      rw [laplace_eq_iteratedFDeriv_complexPlane f]
      simp
      nth_rw 2 [iteratedFDeriv_two_apply]
      simp
      have := (h.differentiableAt one_le_two).fderiv_restrictScalars ℝ
      rw [this]

      sorry
    sorry


theorem holomorphicAt_is_harmonicAt
  {f : ℂ → F}
  {z : ℂ}
  (hf : HolomorphicAt f z) :
  HarmonicAt f z := by

  let t := {x | HolomorphicAt f x}
  have ht : IsOpen t := HolomorphicAt_isOpen f
  have hz : z ∈ t := by exact hf

  constructor
  · -- ContDiffAt ℝ 2 f z
    exact hf.contDiffAt

  · -- Δ f =ᶠ[nhds z] 0
    apply Filter.eventuallyEq_iff_exists_mem.2
    use t
    constructor
    · exact IsOpen.mem_nhds ht hz
    · intro w hw
      unfold Complex.laplace
      simp
      rw [partialDeriv_eventuallyEq ℝ hw.CauchyRiemannAt Complex.I]
      rw [partialDeriv_smul'₂]
      simp

      rw [partialDeriv_commAt hw.contDiffAt Complex.I 1]
      rw [partialDeriv_eventuallyEq ℝ hw.CauchyRiemannAt 1]
      rw [partialDeriv_smul'₂]
      simp

      rw [← smul_assoc]
      simp


theorem re_of_holomorphicAt_is_harmonicAr
  {f : ℂ → ℂ}
  {z : ℂ}
  (h : HolomorphicAt f z) :
  HarmonicAt (Complex.reCLM ∘ f) z := by
  apply harmonicAt_comp_CLM_is_harmonicAt
  exact holomorphicAt_is_harmonicAt h


theorem im_of_holomorphicAt_is_harmonicAt
  {f : ℂ → ℂ}
  {z : ℂ}
  (h : HolomorphicAt f z) :
  HarmonicAt (Complex.imCLM ∘ f) z := by
  apply harmonicAt_comp_CLM_is_harmonicAt
  exact holomorphicAt_is_harmonicAt h


theorem antiholomorphicAt_is_harmonicAt
  {f : ℂ → ℂ}
  {z : ℂ}
  (h : HolomorphicAt f z) :
  HarmonicAt (Complex.conjCLE ∘ f) z := by
  apply harmonicAt_iff_comp_CLE_is_harmonicAt.1
  exact holomorphicAt_is_harmonicAt h


theorem log_normSq_of_holomorphicAt_is_harmonicAt
  {f : ℂ → ℂ}
  {z : ℂ}
  (h₁f : HolomorphicAt f z)
  (h₂f : f z ≠ 0) :
  HarmonicAt (Real.log ∘ Complex.normSq ∘ f) z := by

  -- For later use
  have slitPlaneLemma {z : ℂ} (hz : z ≠ 0) : z ∈ Complex.slitPlane ∨ -z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff, Complex.mem_slitPlane_iff]
    simp at hz
    rw [Complex.ext_iff] at hz
    push_neg at hz
    simp at hz
    simp
    by_contra contra
    push_neg at contra
    exact hz (le_antisymm contra.1.1 contra.2.1) contra.1.2

  -- First prove the theorem for functions with image in the slitPlane
  have lem₁ : ∀ g : ℂ → ℂ, (HolomorphicAt g z) → (g z ≠ 0) → (g z ∈ Complex.slitPlane) → HarmonicAt (Real.log ∘ Complex.normSq ∘ g) z := by
    intro g h₁g h₂g h₃g

    -- Rewrite the log |g|² as Complex.log (g * gc)
    suffices hyp : HarmonicAt (Complex.log ∘ ((Complex.conjCLE ∘ g) * g)) z from by
      have : Real.log ∘ Complex.normSq ∘ g = Complex.reCLM ∘ Complex.ofRealCLM ∘ Real.log ∘ Complex.normSq ∘ g := by
        funext x
        simp
      rw [this]

      have : Complex.ofRealCLM ∘ Real.log ∘ Complex.normSq ∘ g = Complex.log ∘ ((Complex.conjCLE ∘ g) * g) := by
        funext x
        simp
        rw [Complex.ofReal_log]
        rw [Complex.normSq_eq_conj_mul_self]
        exact Complex.normSq_nonneg (g x)
      rw [← this] at hyp
      apply harmonicAt_comp_CLM_is_harmonicAt hyp

    -- Locally around z, rewrite Complex.log (g * gc) as Complex.log g + Complex.log.gc
    -- This uses the assumption that g z is in Complex.slitPlane
    have : (Complex.log ∘ (Complex.conjCLE ∘ g * g)) =ᶠ[nhds z] (Complex.log ∘ Complex.conjCLE ∘ g + Complex.log ∘ g) := by
      apply Filter.eventuallyEq_iff_exists_mem.2
      use g⁻¹' (Complex.slitPlane ∩ {0}ᶜ)
      constructor
      · apply ContinuousAt.preimage_mem_nhds
        · exact h₁g.differentiableAt.continuousAt
        · apply IsOpen.mem_nhds
          apply IsOpen.inter Complex.isOpen_slitPlane isOpen_ne
          constructor
          · exact h₃g
          · exact h₂g
      · intro x hx
        simp
        rw [Complex.log_mul_eq_add_log_iff _ hx.2]
        rw [Complex.arg_conj]
        simp [Complex.slitPlane_arg_ne_pi hx.1]
        constructor
        · exact Real.pi_pos
        · exact Real.pi_nonneg
        simp
        apply hx.2

    -- Locally around z, rewrite Complex.log (g * gc) as Complex.log g + Complex.log.gc
    -- This uses the assumption that g z is in Complex.slitPlane
    have : (Complex.log ∘ (Complex.conjCLE ∘ g * g)) =ᶠ[nhds z] (Complex.conjCLE ∘ Complex.log ∘ g + Complex.log ∘ g) := by
      apply Filter.eventuallyEq_iff_exists_mem.2
      use g⁻¹' (Complex.slitPlane ∩ {0}ᶜ)
      constructor
      · apply ContinuousAt.preimage_mem_nhds
        · exact h₁g.differentiableAt.continuousAt
        · apply IsOpen.mem_nhds
          apply IsOpen.inter Complex.isOpen_slitPlane isOpen_ne
          constructor
          · exact h₃g
          · exact h₂g
      · intro x hx
        simp
        rw [← Complex.log_conj]
        rw [Complex.log_mul_eq_add_log_iff _ hx.2]
        rw [Complex.arg_conj]
        simp [Complex.slitPlane_arg_ne_pi hx.1]
        constructor
        · exact Real.pi_pos
        · exact Real.pi_nonneg
        simp
        apply hx.2
        apply Complex.slitPlane_arg_ne_pi hx.1

    rw [HarmonicAt_eventuallyEq this]
    apply harmonicAt_add_harmonicAt_is_harmonicAt
    · rw [← harmonicAt_iff_comp_CLE_is_harmonicAt]
      apply holomorphicAt_is_harmonicAt
      apply HolomorphicAt_comp
      use Complex.slitPlane, Complex.isOpen_slitPlane.mem_nhds h₃g,
        fun _ a ↦ Complex.differentiableAt_log a
      exact h₁g
    · apply holomorphicAt_is_harmonicAt
      apply HolomorphicAt_comp
      use Complex.slitPlane, Complex.isOpen_slitPlane.mem_nhds h₃g,
        fun _ a ↦ Complex.differentiableAt_log a
      exact h₁g

  by_cases h₃f : f z ∈ Complex.slitPlane
  · exact lem₁ f h₁f h₂f h₃f
  · have : Complex.normSq ∘ f = Complex.normSq ∘ (-f) := by funext; simp
    rw [this]
    apply lem₁ (-f)
    · exact HolomorphicAt_neg h₁f
    · simpa
    · exact (slitPlaneLemma h₂f).resolve_left h₃f


theorem logabs_of_holomorphicAt_is_harmonic
  {f : ℂ → ℂ}
  {z : ℂ}
  (h₁f : HolomorphicAt f z)
  (h₂f : f z ≠ 0) :
  HarmonicAt (fun w ↦ Real.log ‖f w‖) z := by

  -- Suffices: Harmonic (2⁻¹ • Real.log ∘ ⇑Complex.normSq ∘ f)
  have : (fun z ↦ Real.log ‖f z‖) = (2 : ℝ)⁻¹ • (Real.log ∘ Complex.normSq ∘ f) := by
    funext z
    simp
    rw [Complex.norm_def]
    rw [Real.log_sqrt]
    linarith
    exact Complex.normSq_nonneg (f z)
  rw [this]

  -- Suffices: Harmonic (Real.log ∘ ⇑Complex.normSq ∘ f)
  apply (harmonicAt_iff_smul_const_is_harmonicAt (inv_ne_zero two_ne_zero)).1
  exact log_normSq_of_holomorphicAt_is_harmonicAt h₁f h₂f
