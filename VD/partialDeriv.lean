import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Defs.Filter

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

noncomputable def partialDeriv : E → (E → F) → (E → F) :=
  fun v ↦ (fun f ↦ (fun w ↦ fderiv 𝕜 f w v))

theorem partialDeriv_eventuallyEq' {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[nhds x] f₂) :
    ∀ v : E, partialDeriv 𝕜 v f₁ =ᶠ[nhds x] partialDeriv 𝕜 v f₂ := by
  unfold partialDeriv
  intro v
  apply Filter.EventuallyEq.comp₂
  exact Filter.EventuallyEq.fderiv h
  simp

theorem partialDeriv_eventuallyEq {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[nhds x] f₂) :
    ∀ v : E, partialDeriv 𝕜 v f₁ x = partialDeriv 𝕜 v f₂ x := by
  unfold partialDeriv
  rw [Filter.EventuallyEq.fderiv_eq h]
  intro v
  simp

theorem partialDeriv_smul₁ {f : E → F} {a : 𝕜} {v : E} :
    partialDeriv 𝕜 (a • v) f = a • partialDeriv 𝕜 v f := by
  unfold partialDeriv
  conv =>
    left
    intro w
    rw [map_smul]
  funext w
  simp

theorem partialDeriv_add₁ {f : E → F} {v₁ v₂ : E} :
    partialDeriv 𝕜 (v₁ + v₂) f = (partialDeriv 𝕜 v₁ f) + (partialDeriv 𝕜 v₂ f) := by
  unfold partialDeriv
  conv =>
    left
    intro w
    rw [map_add]
  funext w
  simp

theorem partialDeriv_smul₂ {f : E → F} {a : 𝕜} {v : E} :
    partialDeriv 𝕜 v (a • f) = a • partialDeriv 𝕜 v f := by
  unfold partialDeriv
  funext w
  have : a • f = fun y ↦ a • f y := by rfl
  rw [this]
  by_cases ha : a = 0
  · rw [ha]
    simp
  · by_cases hf : DifferentiableAt 𝕜 f w
    · rw [fderiv_fun_const_smul hf]
      simp
    · have : ¬DifferentiableAt 𝕜 (fun y => a • f y) w := by
        by_contra contra
        let ZZ := DifferentiableAt.fun_const_smul contra a⁻¹
        have : (fun y => a⁻¹ • a • f y) = f := by
          funext i
          rw [← smul_assoc, smul_eq_mul, mul_comm, mul_inv_cancel₀ ha]
          simp
        rw [this] at ZZ
        exact hf ZZ
      simp
      rw [fderiv_zero_of_not_differentiableAt hf]
      rw [fderiv_zero_of_not_differentiableAt this]
      simp

theorem partialDeriv_add₂ {f₁ f₂ : E → F} (h₁ : Differentiable 𝕜 f₁) (h₂ : Differentiable 𝕜 f₂) :
    ∀ v : E, partialDeriv 𝕜 v (f₁ + f₂) = (partialDeriv 𝕜 v f₁) + (partialDeriv 𝕜 v f₂) := by
  unfold partialDeriv
  intro v
  have : f₁ + f₂ = fun y ↦ f₁ y + f₂ y := by rfl
  rw [this]
  conv =>
    left
    intro w
    left
    rw [fderiv_fun_add (h₁ w) (h₂ w)]
  funext w
  simp

theorem partialDeriv_add₂_differentiableAt {f₁ f₂ : E → F} {v x : E}
    (h₁ : DifferentiableAt 𝕜 f₁ x) (h₂ : DifferentiableAt 𝕜 f₂ x) :
    partialDeriv 𝕜 v (f₁ + f₂) x = (partialDeriv 𝕜 v f₁) x + (partialDeriv 𝕜 v f₂) x := by
  unfold partialDeriv
  have : f₁ + f₂ = fun y ↦ f₁ y + f₂ y := by rfl
  rw [this]
  rw [fderiv_fun_add h₁ h₂]
  rfl

theorem partialDeriv_add₂_contDiffAt {f₁ f₂ : E → F} {v x : E}
    (h₁ : ContDiffAt 𝕜 1 f₁ x) (h₂ : ContDiffAt 𝕜 1 f₂ x) :
    partialDeriv 𝕜 v (f₁ + f₂) =ᶠ[nhds x] (partialDeriv 𝕜 v f₁) + (partialDeriv 𝕜 v f₂) := by
  obtain ⟨f₁', u₁, hu₁, _, hf₁'⟩ := contDiffAt_one_iff.1 h₁
  obtain ⟨f₂', u₂, hu₂, _, hf₂'⟩ := contDiffAt_one_iff.1 h₂
  apply Filter.eventuallyEq_iff_exists_mem.2
  use u₁ ∩ u₂, Filter.inter_mem hu₁ hu₂
  intro x hx
  simp
  apply partialDeriv_add₂_differentiableAt 𝕜
  exact (hf₁' x hx.1).differentiableAt
  exact (hf₂' x hx.2).differentiableAt

theorem partialDeriv_sub₂ {f₁ f₂ : E → F} (h₁ : Differentiable 𝕜 f₁) (h₂ : Differentiable 𝕜 f₂) :
    ∀ v : E, partialDeriv 𝕜 v (f₁ - f₂) = (partialDeriv 𝕜 v f₁) - (partialDeriv 𝕜 v f₂) := by
  unfold partialDeriv
  intro v
  have : f₁ - f₂ = fun y ↦ f₁ y - f₂ y := by rfl
  rw [this]
  conv =>
    left
    intro w
    left
    rw [fderiv_fun_sub (h₁ w) (h₂ w)]
  funext w
  simp

theorem partialDeriv_sub₂_differentiableAt {f₁ f₂ : E → F} {v x : E}
    (h₁ : DifferentiableAt 𝕜 f₁ x) (h₂ : DifferentiableAt 𝕜 f₂ x) :
    partialDeriv 𝕜 v (f₁ - f₂) x = (partialDeriv 𝕜 v f₁) x - (partialDeriv 𝕜 v f₂) x := by
  unfold partialDeriv
  have : f₁ - f₂ = fun y ↦ f₁ y - f₂ y := by rfl
  rw [this]
  rw [fderiv_fun_sub h₁ h₂]
  rfl

theorem partialDeriv_sub₂_contDiffAt {f₁ f₂ : E → F} {v x : E}
    (h₁ : ContDiffAt 𝕜 1 f₁ x) (h₂ : ContDiffAt 𝕜 1 f₂ x) :
    partialDeriv 𝕜 v (f₁ - f₂) =ᶠ[nhds x] (partialDeriv 𝕜 v f₁) - (partialDeriv 𝕜 v f₂) := by
  obtain ⟨f₁', u₁, hu₁, _, hf₁'⟩ := contDiffAt_one_iff.1 h₁
  obtain ⟨f₂', u₂, hu₂, _, hf₂'⟩ := contDiffAt_one_iff.1 h₂
  apply Filter.eventuallyEq_iff_exists_mem.2
  use u₁ ∩ u₂
  constructor
  · exact Filter.inter_mem hu₁ hu₂
  · intro x hx
    simp
    apply partialDeriv_sub₂_differentiableAt 𝕜
    exact (hf₁' x (Set.mem_of_mem_inter_left hx)).differentiableAt
    exact (hf₂' x (Set.mem_of_mem_inter_right hx)).differentiableAt

theorem partialDeriv_compContLin {f : E → F} {l : F →L[𝕜] G} {v : E}
    (h : Differentiable 𝕜 f) :
  partialDeriv 𝕜 v (l ∘ f) = l ∘ partialDeriv 𝕜 v f := by
  unfold partialDeriv
  conv =>
    left
    intro w
    left
    rw [fderiv_comp w (ContinuousLinearMap.differentiableAt l) (h w)]
  simp
  rfl

theorem partialDeriv_compContLinAt {f : E → F} {l : F →L[𝕜] G} {v x : E}
    (h : DifferentiableAt 𝕜 f x) :
    (partialDeriv 𝕜 v (l ∘ f)) x = (l ∘ partialDeriv 𝕜 v f) x:= by
  unfold partialDeriv
  rw [fderiv_comp x (ContinuousLinearMap.differentiableAt l) h]
  simp

theorem partialDeriv_compCLE {f : E → F} {l : F ≃L[𝕜] G} {v : E} :
    partialDeriv 𝕜 v (l ∘ f) = l ∘ partialDeriv 𝕜 v f := by
  funext x
  by_cases hyp : DifferentiableAt 𝕜 f x
  · let lCLM : F →L[𝕜] G := l
    suffices shyp : partialDeriv 𝕜 v (lCLM ∘ f) x = (lCLM ∘ partialDeriv 𝕜 v f) x from by tauto
    apply partialDeriv_compContLinAt
    exact hyp
  · unfold partialDeriv
    rw [fderiv_zero_of_not_differentiableAt]
    simp
    rw [fderiv_zero_of_not_differentiableAt]
    simp
    exact hyp
    rw [ContinuousLinearEquiv.comp_differentiableAt_iff]
    exact hyp

@[simp]
theorem partialDeriv_contDiff {n : ℕ} {f : E → F} (h : ContDiff 𝕜 (n + 1) f) :
    ∀ v : E, ContDiff 𝕜 n (partialDeriv 𝕜 v f) := by
  unfold partialDeriv
  intro v
  let A := (contDiff_succ_iff_fderiv.1 h).right
  simp at A
  have : (fun w => (fderiv 𝕜 f w) v) = (fun f => f v) ∘ (fun w => (fderiv 𝕜 f w)) := by
    rfl
  rw [this]
  refine ContDiff.comp ?hg A
  refine ContDiff.of_succ ?hg.h
  refine ContDiff.clm_apply ?hg.h.hf ?hg.h.hg
  exact contDiff_id
  exact contDiff_const

theorem partialDeriv_contDiffAt {n : ℕ} {f : E → F} {x : E} (h : ContDiffAt 𝕜 (n + 1) f x) :
    ∀ v : E, ContDiffAt 𝕜 n (partialDeriv 𝕜 v f) x := by
  unfold partialDeriv
  intro v
  let eval_at_v : (E →L[𝕜] F) →L[𝕜] F :=
  {
    toFun := fun l ↦ l v
    map_add' := by simp
    map_smul' := by simp
  }
  have : (fun w => (fderiv 𝕜 f w) v) = eval_at_v ∘ (fun w => (fderiv 𝕜 f w)) := by
    rfl
  rw [this]
  apply ContDiffAt.continuousLinearMap_comp
  -- ContDiffAt 𝕜 (↑n) (fun w => fderiv 𝕜 f w) x
  apply ContDiffAt.fderiv_right h
  rfl

lemma partialDeriv_fderiv {f : E → F} (hf : ContDiff 𝕜 2 f) (z a b : E) :
    fderiv 𝕜 (fderiv 𝕜 f) z b a = partialDeriv 𝕜 b (partialDeriv 𝕜 a f) z := by
  unfold partialDeriv
  rw [fderiv_clm_apply]
  · simp
  · apply Differentiable.differentiableAt
    rw [← one_add_one_eq_two] at hf
    rw [contDiff_succ_iff_fderiv] at hf
    apply hf.2.2.differentiable
    simp
  · simp

lemma partialDeriv_fderivOn {s : Set E} {f : E → F} (hs : IsOpen s)
    (hf : ContDiffOn 𝕜 2 f s) (a b : E) :
    ∀ z ∈ s, fderiv 𝕜 (fderiv 𝕜 f) z b a = partialDeriv 𝕜 b (partialDeriv 𝕜 a f) z := by
  intro z hz
  unfold partialDeriv
  rw [fderiv_clm_apply]
  · simp
  · convert DifferentiableOn.differentiableAt _ (IsOpen.mem_nhds hs hz)
    apply ContDiffOn.differentiableOn _ (Preorder.le_refl 1)
    rw [← one_add_one_eq_two] at hf
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hs] at hf
    exact hf.2.2
  · simp

lemma partialDeriv_fderivAt {z : E} {f : E → F} (hf : ContDiffAt 𝕜 2 f z) (a b : E) :
  fderiv 𝕜 (fderiv 𝕜 f) z b a = partialDeriv 𝕜 b (partialDeriv 𝕜 a f) z := by
  unfold partialDeriv
  rw [fderiv_clm_apply]
  simp

  -- DifferentiableAt 𝕜 (fun w => fderiv 𝕜 f w) z
  obtain ⟨f', ⟨u, h₁u, h₂u⟩, hf' ⟩ := contDiffAt_succ_iff_hasFDerivAt.1 hf
  have t₁ : (fun w ↦ fderiv 𝕜 f w) =ᶠ[nhds z] f' := by
    apply Filter.eventuallyEq_iff_exists_mem.2
    use u
    constructor
    · exact h₁u
    · intro x hx
      exact HasFDerivAt.fderiv (h₂u x hx)
  rw [Filter.EventuallyEq.differentiableAt_iff t₁]
  exact hf'.differentiableAt le_rfl

  -- DifferentiableAt 𝕜 (fun w => a) z
  exact differentiableAt_const a


section restrictScalars

theorem partialDeriv_smul'₂
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]
  {f : E → F} {a : 𝕜'} {v : E} :
  partialDeriv 𝕜 v (a • f) = a • partialDeriv 𝕜 v f := by

  funext w
  by_cases ha : a = 0
  · unfold partialDeriv
    have : a • f = fun y ↦ a • f y := by rfl
    rw [this, ha]
    simp
  · -- Now a is not zero. We present scalar multiplication with a as a continuous linear equivalence.
    let smulCLM : F ≃L[𝕜] F :=
    {
      toFun := fun x ↦ a • x
      map_add' := fun x y => DistribSMul.smul_add a x y
      map_smul' := fun m x => (smul_comm ((RingHom.id 𝕜) m) a x).symm
      invFun := fun x ↦ a⁻¹ • x
      left_inv := by
        intro x
        simp
        rw [← smul_assoc, smul_eq_mul, mul_comm, mul_inv_cancel₀ ha, one_smul]
      right_inv := by
        intro x
        simp
        rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ ha, one_smul]
      continuous_toFun := continuous_const_smul a
      continuous_invFun := continuous_const_smul a⁻¹
    }

    have : a • f = smulCLM ∘ f := by tauto
    rw [this]
    rw [partialDeriv_compCLE]
    tauto


theorem partialDeriv_restrictScalars
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]
  {f : E → F} {v : E} :
  Differentiable 𝕜' f → partialDeriv 𝕜 v f = partialDeriv 𝕜' v f := by
  intro hf
  unfold partialDeriv
  funext x
  rw [(hf x).fderiv_restrictScalars 𝕜]
  simp


theorem partialDeriv_comm
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} (h : ContDiff ℝ 2 f) :
  ∀ v₁ v₂ : E, partialDeriv ℝ v₁ (partialDeriv ℝ v₂ f) = partialDeriv ℝ v₂ (partialDeriv ℝ v₁ f) := by

  intro v₁ v₂
  funext z

  have derivSymm :
    (fderiv ℝ (fun w => fderiv ℝ f w) z) v₁ v₂ = (fderiv ℝ (fun w => fderiv ℝ f w) z) v₂ v₁ := by

    let f' := fderiv ℝ f
    have h₀ : ∀ y, HasFDerivAt f (f' y) y := by
      intro y
      exact DifferentiableAt.hasFDerivAt ((h.differentiable one_le_two) y)

    let f'' := (fderiv ℝ f' z)
    have h₁ : HasFDerivAt f' f'' z := by
      apply DifferentiableAt.hasFDerivAt
      rw [← one_add_one_eq_two] at h
      apply (contDiff_succ_iff_fderiv.1 h).2.2.differentiable (Preorder.le_refl 1)

    apply second_derivative_symmetric h₀ h₁ v₁ v₂

  rw [← partialDeriv_fderiv ℝ h z v₂ v₁]
  rw [derivSymm]
  rw [partialDeriv_fderiv ℝ h z v₁ v₂]

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}

theorem partialDeriv_commOn {s : Set E} (hs : IsOpen s) (h : ContDiffOn ℝ 2 f s) :
    ∀ v₁ v₂ : E, ∀ z ∈ s,
      partialDeriv ℝ v₁ (partialDeriv ℝ v₂ f) z = partialDeriv ℝ v₂ (partialDeriv ℝ v₁ f) z := by
  intro v₁ v₂ z hz
  have derivSymm :
    (fderiv ℝ (fun w => fderiv ℝ f w) z) v₁ v₂ = (fderiv ℝ (fun w => fderiv ℝ f w) z) v₂ v₁ := by
    let f' := fderiv ℝ f
    have h₀1 : ∀ y ∈ s, HasFDerivAt f (f' y) y := by
      intro y hy
      apply DifferentiableAt.hasFDerivAt
      apply DifferentiableOn.differentiableAt _ (IsOpen.mem_nhds hs hy)
      apply h.differentiableOn one_le_two
    let f'' := (fderiv ℝ f' z)
    have h₁ : HasFDerivAt f' f'' z := by
      apply DifferentiableAt.hasFDerivAt
      apply DifferentiableOn.differentiableAt _ (IsOpen.mem_nhds hs hz)
      apply ContDiffOn.differentiableOn _ (Preorder.le_refl 1)
      rw [← one_add_one_eq_two] at h
      exact ((contDiffOn_succ_iff_fderiv_of_isOpen hs).1 h).2.2
    have h₀' : ∀ᶠ (y : E) in nhds z, HasFDerivAt f (f' y) y := by
      apply eventually_nhds_iff.mpr
      use s
    exact second_derivative_symmetric_of_eventually h₀' h₁ v₁ v₂
  rw [← partialDeriv_fderivOn ℝ hs h v₂ v₁ z hz]
  rw [derivSymm]
  rw [← partialDeriv_fderivOn ℝ hs h v₁ v₂ z hz]

theorem partialDeriv_commAt {z : E} {f : E → F} (h : ContDiffAt ℝ 2 f z) :
    ∀ v₁ v₂ : E,
      partialDeriv ℝ v₁ (partialDeriv ℝ v₂ f) z = partialDeriv ℝ v₂ (partialDeriv ℝ v₁ f) z := by
  let A := h.contDiffOn le_rfl
  simp at A
  obtain ⟨u, hu₁, hu₂⟩ := A
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := mem_nhds_iff.1 hu₁
  intro v₁ v₂
  exact partialDeriv_commOn hv₂ (hu₂.mono hv₁) v₁ v₂ z hv₃
