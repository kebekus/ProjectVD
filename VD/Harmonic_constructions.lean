import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import VD.Harmonic

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : ℂ → F}
  {s t : Set E} {c : ℝ}

open Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem fxx {n : ℕ} {x : E}
    {f : E → (ContinuousMultilinearMap ℂ (fun i : Fin n ↦ E) F)}
    (h : DifferentiableAt ℂ f x) :
    (fderiv ℝ ((ContinuousMultilinearMap.restrictScalarsLinear ℝ) ∘ f) x)
      = (ContinuousMultilinearMap.restrictScalars ℝ) ∘ ((fderiv ℂ f x).restrictScalars ℝ) := by
  rw [fderiv_comp]
  rw [ContinuousLinearMap.fderiv]
  simp
  ext a b
  simp
  have := h.fderiv_restrictScalars ℝ
  rw [this]
  simp
  fun_prop
  exact h.restrictScalars ℝ


theorem ContDiffAt.differentiableAt_iteratedDeriv
    {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {F : Type u_2} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → F} {x : 𝕜} {n : WithTop ℕ∞} {m : ℕ}
    (h : ContDiffAt 𝕜 n f x) (hmn : m < n) :
    DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 m f) x := by
  apply ContDiffAt.differentiableAt (n := 1)
  apply h.iteratedFDeriv_right (i := m) (m := 1)
  · refine add_le_of_le_tsub_left_of_le ?_ ?_
    · sorry
    · sorry
  · rfl

theorem ContDiffAt.iteratedFDeriv_restrictScalars {f : E → F} {n : ℕ} {z : E}
    (h : ContDiffAt ℂ n f z) :
    (ContinuousMultilinearMap.restrictScalarsLinear ℝ) ∘ (iteratedFDeriv ℂ n f) =ᶠ[𝓝 z]
      (iteratedFDeriv ℝ n f) := by
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
    rw [← Filter.EventuallyEq] at h₁a
    ext m
    simp [iteratedFDeriv_succ_apply_left]
    have := h₁a.fderiv_eq (𝕜 := ℝ)
    rw [← this]
    rw [fxx]
    simp
    · have := h.differentiableAt_iteratedDeriv (m := n)

      sorry


theorem ContDiffAt.harmonicAt  {f : ℂ → F} {x : ℂ} (h : ContDiffAt ℂ 2 f x) :
    HarmonicAt f x := by
  constructor
  · exact ContDiffAt.restrict_scalars ℝ h
  · filter_upwards [h.iteratedFDeric_restrictScalars] with a ha
    rw [laplace_eq_iteratedFDeriv_complexPlane f]
    simp
    rw [← ha]
    simp

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
