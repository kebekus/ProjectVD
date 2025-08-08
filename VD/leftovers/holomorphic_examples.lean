import VD.harmonicAt
import VD.holomorphicAt
import VD.holomorphic_primitive

theorem CauchyRiemann₆
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f : E → F}
  {z : E} :
  (DifferentiableAt ℂ f z) ↔ (DifferentiableAt ℝ f z) ∧ ∀ e, partialDeriv ℝ (Complex.I • e) f z = Complex.I • partialDeriv ℝ e f z := by
  constructor

  · -- Direction "→"
    intro h
    constructor
    · exact DifferentiableAt.restrictScalars ℝ h
    · unfold partialDeriv
      conv =>
        intro e
        left
        rw [DifferentiableAt.fderiv_restrictScalars ℝ h]
        simp
        rw [← mul_one Complex.I]
        rw [← smul_eq_mul]
      conv =>
        intro e
        right
        right
        rw [DifferentiableAt.fderiv_restrictScalars ℝ h]
      simp

  · -- Direction "←"
    intro ⟨h₁, h₂⟩
    apply (differentiableAt_iff_restrictScalars ℝ h₁).2

    use {
      toFun := fderiv ℝ f z
      map_add' := fun x y => ContinuousLinearMap.map_add (fderiv ℝ f z) x y
      map_smul' := by
        simp
        intro m x
        have : m = m.re + m.im • Complex.I := by simp
        rw [this, add_smul, add_smul, ContinuousLinearMap.map_add]
        congr
        simp only [Complex.coe_smul, map_smul]
        rw [smul_assoc, smul_assoc, ContinuousLinearMap.map_smul (fderiv ℝ f z) m.2]
        congr
        exact h₂ x
    }
    rfl


theorem CauchyRiemann₇
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f : ℂ → F}
  {z : ℂ} :
  (DifferentiableAt ℂ f z) ↔ (DifferentiableAt ℝ f z) ∧ partialDeriv ℝ Complex.I f z = Complex.I • partialDeriv ℝ 1 f z := by
  constructor
  · intro hf
    constructor
    · exact (CauchyRiemann₆.1 hf).1
    · let A := (CauchyRiemann₆.1 hf).2 1
      simp at A
      exact A
  · intro ⟨h₁, h₂⟩
    apply CauchyRiemann₆.2
    constructor
    · exact h₁
    · intro e
      have : Complex.I • e = e • Complex.I := by
        rw [smul_eq_mul, smul_eq_mul]
        exact CommMonoid.mul_comm Complex.I e
      rw [this]
      have : e = e.re + e.im • Complex.I := by simp
      rw [this, add_smul, partialDeriv_add₁, partialDeriv_add₁]
      simp
      rw [← smul_eq_mul]
      have : partialDeriv ℝ ((e.re : ℝ) • Complex.I) f = partialDeriv ℝ ((e.re : ℂ) • Complex.I) f := by rfl
      rw [← this, partialDeriv_smul₁ ℝ]
      have : (e.re : ℂ) = (e.re : ℝ) • (1 : ℂ) := by simp
      rw [this, partialDeriv_smul₁ ℝ]
      have : partialDeriv ℝ ((e.im : ℂ) * Complex.I) f = partialDeriv ℝ ((e.im : ℝ) • Complex.I) f := by rfl
      rw [this, partialDeriv_smul₁ ℝ]
      simp
      rw [h₂]
      rw [smul_comm]
      congr
      rw [mul_assoc]
      simp
      nth_rw 2 [smul_comm]
      rw [← smul_assoc]
      simp
      have : - (e.im : ℂ) = (-e.im : ℝ) • (1 : ℂ) := by simp
      rw [this, partialDeriv_smul₁ ℝ]
      simp

/-

A harmonic, real-valued function on ℂ is the real part of a suitable holomorphic
function.

-/

theorem harmonic_is_realOfHolomorphic
  {f : ℂ → ℝ}
  {z : ℂ}
  {R : ℝ}
  (hR : 0 < R)
  (hf : ∀ x ∈ Metric.ball z R, HarmonicAt f x) :
  ∃ F, (∀ x ∈ Metric.ball z R, HolomorphicAt F x) ∧ (Set.EqOn (Complex.reCLM ∘ F) f (Metric.ball z R)) := by

  let f_1 : ℂ → ℂ := Complex.ofRealCLM ∘ (partialDeriv ℝ 1 f)
  let f_I : ℂ → ℂ := Complex.ofRealCLM ∘ (partialDeriv ℝ Complex.I f)

  let g : ℂ → ℂ := f_1 - Complex.I • f_I

  have contDiffOn_if_contDiffAt
    {f' : ℂ → ℝ}
    {z' : ℂ}
    {R' : ℝ}
    {n' : ℕ}
    (hf' : ∀ x ∈ Metric.ball z' R', ContDiffAt ℝ n' f' x) :
    ContDiffOn ℝ n' f' (Metric.ball z' R') := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    exact hf' z hz

  have reg₂f : ContDiffOn ℝ 2 f (Metric.ball z R) := by
    apply contDiffOn_if_contDiffAt
    intro x hx
    exact (hf x hx).1

  have contDiffOn_if_contDiffAt'
    {f' : ℂ → ℂ}
    {z' : ℂ}
    {R' : ℝ}
    {n' : ℕ}
    (hf' : ∀ x ∈ Metric.ball z' R', ContDiffAt ℝ n' f' x) :
    ContDiffOn ℝ n' f' (Metric.ball z' R') := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    exact hf' z hz

  have reg₁f_1 : ContDiffOn ℝ 1 f_1 (Metric.ball z R) := by
    apply contDiffOn_if_contDiffAt'
    intro z hz
    dsimp [f_1]
    apply ContDiffAt.continuousLinearMap_comp
    exact partialDeriv_contDiffAt ℝ (hf z hz).1 1

  have reg₁f_I : ContDiffOn ℝ 1 f_I (Metric.ball z R) := by
    apply contDiffOn_if_contDiffAt'
    intro z hz
    dsimp [f_I]
    apply ContDiffAt.continuousLinearMap_comp
    exact partialDeriv_contDiffAt ℝ (hf z hz).1 Complex.I

  have reg₁g : ContDiffOn ℝ 1 g (Metric.ball z R) := by
    dsimp [g]
    apply ContDiffOn.sub
    exact reg₁f_1
    have : Complex.I • f_I = fun x ↦ Complex.I • f_I x := by rfl
    rw [this]
    apply ContDiffOn.const_smul
    exact reg₁f_I

  have reg₁ : DifferentiableOn ℂ g (Metric.ball z R) := by
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply CauchyRiemann₇.2
    constructor
    · apply DifferentiableWithinAt.differentiableAt (reg₁g.differentiableOn le_rfl x hx)
      apply IsOpen.mem_nhds Metric.isOpen_ball hx
    · dsimp [g]
      rw [partialDeriv_sub₂_differentiableAt, partialDeriv_sub₂_differentiableAt]
      dsimp [f_1, f_I]
      rw [partialDeriv_smul'₂, partialDeriv_smul'₂]
      rw [partialDeriv_compContLinAt, partialDeriv_compContLinAt]
      simp
      rw [partialDeriv_compContLinAt, partialDeriv_compContLinAt]
      rw [mul_sub]
      simp
      rw [← mul_assoc]
      simp
      rw [add_comm, sub_eq_add_neg]
      congr 1
      · rw [partialDeriv_commOn _ reg₂f Complex.I 1]
        exact hx
        exact Metric.isOpen_ball
      · let A := Filter.EventuallyEq.eq_of_nhds (hf x hx).2
        simp at A
        unfold Complex.laplace at A
        conv =>
          right
          right
          rw [← sub_zero (partialDeriv ℝ 1 (partialDeriv ℝ 1 f) x)]
          rw [← A]
        simp

      --DifferentiableAt ℝ (partialDeriv ℝ _ f)
      repeat
        apply ContDiffAt.differentiableAt (n := 1)
        apply partialDeriv_contDiffAt ℝ (hf x hx).1
        apply le_rfl

      -- DifferentiableAt ℝ f_1 x
      apply (reg₁f_1.differentiableOn le_rfl).differentiableAt
      apply IsOpen.mem_nhds Metric.isOpen_ball hx

      -- DifferentiableAt ℝ (Complex.I • f_I)
      have : Complex.I • f_I = fun x ↦ Complex.I • f_I x := by rfl
      rw [this]
      apply DifferentiableAt.fun_const_smul
      apply (reg₁f_I.differentiableOn le_rfl).differentiableAt
      apply IsOpen.mem_nhds Metric.isOpen_ball hx

      -- Differentiable ℝ f_1
      apply (reg₁f_1.differentiableOn le_rfl).differentiableAt
      apply IsOpen.mem_nhds Metric.isOpen_ball hx

      -- Differentiable ℝ (Complex.I • f_I)
      have : Complex.I • f_I = fun x ↦ Complex.I • f_I x := by rfl
      rw [this]
      apply DifferentiableAt.fun_const_smul
      apply (reg₁f_I.differentiableOn le_rfl).differentiableAt
      apply IsOpen.mem_nhds Metric.isOpen_ball hx

  let F := fun z' ↦ (primitive z g) z' + f z

  have regF : DifferentiableOn ℂ F (Metric.ball z R) := by
    apply DifferentiableOn.add
    apply primitive_differentiableOn reg₁
    simp

  have pF'' : ∀ x ∈ Metric.ball z R, (fderiv ℝ F x) = ContinuousLinearMap.lsmul ℝ ℂ (g x) := by
    intro x hx
    have : DifferentiableAt ℂ F x := by
      apply (regF x hx).differentiableAt
      apply IsOpen.mem_nhds Metric.isOpen_ball hx
    rw [DifferentiableAt.fderiv_restrictScalars ℝ this]
    dsimp [F]
    rw [fderiv_add_const]
    rw [primitive_fderiv' reg₁ x hx]
    exact rfl

  use F

  constructor
  · -- ∀ x ∈ Metric.ball z R, HolomorphicAt F x
    intro x hx
    apply HolomorphicAt_iff.2
    use Metric.ball z R
    constructor
    · exact Metric.isOpen_ball
    · constructor
      · assumption
      · intro w hw
        apply (regF w hw).differentiableAt
        apply IsOpen.mem_nhds Metric.isOpen_ball hw
  · -- Set.EqOn (⇑Complex.reCLM ∘ F) f (Metric.ball z R)
    have : DifferentiableOn ℝ (Complex.reCLM ∘ F) (Metric.ball z R) := by
      apply DifferentiableOn.comp
      apply Differentiable.differentiableOn
      apply ContinuousLinearMap.differentiable Complex.reCLM
      apply regF.restrictScalars ℝ
      exact Set.mapsTo'.mpr fun ⦃a⦄ _ => hR
    have hz : z ∈ Metric.ball z R := by exact Metric.mem_ball_self hR
    apply Convex.eqOn_of_fderivWithin_eq _ this _ _ _ hz _
    exact convex_ball z R
    apply reg₂f.differentiableOn one_le_two
    apply IsOpen.uniqueDiffOn Metric.isOpen_ball

    intro x hx
    rw [fderivWithin_eq_fderiv, fderivWithin_eq_fderiv]
    rw [fderiv_comp]
    simp
    apply ContinuousLinearMap.ext
    intro w
    simp
    rw [pF'']
    dsimp [g, f_1, f_I, partialDeriv]
    simp
    have : w = w.re • 1 + w.im • Complex.I := by simp
    nth_rw 3 [this]
    rw [(fderiv ℝ f x).map_add]
    rw [(fderiv ℝ f x).map_smul, (fderiv ℝ f x).map_smul]
    rw [smul_eq_mul, smul_eq_mul]
    ring

    assumption
    exact ContinuousLinearMap.differentiableAt Complex.reCLM
    apply (regF.restrictScalars ℝ  x hx).differentiableAt
    apply IsOpen.mem_nhds Metric.isOpen_ball hx
    apply IsOpen.uniqueDiffOn Metric.isOpen_ball
    assumption
    apply (reg₂f.differentiableOn one_le_two).differentiableAt
    apply IsOpen.mem_nhds Metric.isOpen_ball hx
    apply IsOpen.uniqueDiffOn Metric.isOpen_ball
    assumption
    -- DifferentiableAt ℝ (⇑Complex.reCLM ∘ F) x
    apply DifferentiableAt.comp
    apply Differentiable.differentiableAt
    exact ContinuousLinearMap.differentiable Complex.reCLM
    apply (regF.restrictScalars ℝ  x hx).differentiableAt
    apply IsOpen.mem_nhds Metric.isOpen_ball hx
    --
    dsimp [F]
    rw [primitive_zeroAtBasepoint]
    simp
