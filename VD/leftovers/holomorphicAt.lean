import Mathlib.Analysis.Complex.CauchyIntegral
import VD.cauchyRiemann

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

def HolomorphicAt (f : E → F) (x : E) : Prop :=
  ∃ s ∈ nhds x, ∀ z ∈ s, DifferentiableAt ℂ f z


theorem HolomorphicAt_iff
  {f : E → F}
  {x : E} :
  HolomorphicAt f x ↔ ∃ s :
  Set E, IsOpen s ∧ x ∈ s ∧ (∀ z ∈ s, DifferentiableAt ℂ f z) := by
  constructor
  · intro hf
    obtain ⟨t, h₁t, h₂t⟩ := hf
    obtain ⟨s, h₁s, h₂s, h₃s⟩ := mem_nhds_iff.1 h₁t
    use s
    constructor
    · assumption
    · constructor
      · assumption
      · intro z hz
        exact h₂t z (h₁s hz)
  · intro hyp
    obtain ⟨s, h₁s, h₂s, hf⟩ := hyp
    use s
    constructor
    · apply (IsOpen.mem_nhds_iff h₁s).2 h₂s
    · assumption


theorem Differentiable.holomorphicAt
  {f : E → F}
  (hf : Differentiable ℂ f)
  {x : E} :
  HolomorphicAt f x := by
  apply HolomorphicAt_iff.2
  use Set.univ
  constructor
  · exact isOpen_univ
  · constructor
    · exact trivial
    · intro z _
      exact hf z


theorem HolomorphicAt_isOpen
  (f : E → F) :
  IsOpen { x : E | HolomorphicAt f x } := by

  rw [← subset_interior_iff_isOpen]
  intro x hx
  simp at hx
  obtain ⟨s, h₁s, h₂s, h₃s⟩ := HolomorphicAt_iff.1 hx
  use s
  constructor
  · simp
    constructor
    · exact h₁s
    · intro x hx
      simp
      use s
      constructor
      · exact IsOpen.mem_nhds h₁s hx
      · exact h₃s
  · exact h₂s


theorem HolomorphicAt_comp
  {g : E → F}
  {f : F → G}
  {z : E}
  (hf : HolomorphicAt f (g z))
  (hg : HolomorphicAt g z) :
  HolomorphicAt (f ∘ g) z := by
  obtain ⟨UE, h₁UE, h₂UE⟩ := hg
  obtain ⟨UF, h₁UF, h₂UF⟩ := hf
  use UE ∩ g⁻¹' UF
  constructor
  · simp
    constructor
    · assumption
    · apply ContinuousAt.preimage_mem_nhds
      apply (h₂UE z (mem_of_mem_nhds h₁UE)).continuousAt
      assumption
  · intro x hx
    apply DifferentiableAt.comp
    apply h₂UF
    exact hx.2
    apply h₂UE
    exact hx.1


theorem HolomorphicAt_neg
  {f : E → F}
  {z : E}
  (hf : HolomorphicAt f z) :
  HolomorphicAt (-f) z := by
  obtain ⟨UF, h₁UF, h₂UF⟩ := hf
  use UF
  constructor
  · assumption
  · intro z hz
    apply differentiableAt_neg_iff.mp
    simp
    exact h₂UF z hz


theorem HolomorphicAt.analyticAt
  [CompleteSpace F]
  {f : ℂ → F}
  {x : ℂ} :
  HolomorphicAt f x → AnalyticAt ℂ f x := by
  intro hf
  obtain ⟨s, h₁s, h₂s, h₃s⟩ := HolomorphicAt_iff.1 hf
  apply DifferentiableOn.analyticAt (s := s)
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply h₃s
  exact hz
  exact IsOpen.mem_nhds h₁s h₂s


theorem AnalyticAt.holomorphicAt
  [CompleteSpace F]
  {f : ℂ → F}
  {x : ℂ} :
  AnalyticAt ℂ f x → HolomorphicAt f x := by
  intro hf
  rw [HolomorphicAt_iff]
  use {x : ℂ | AnalyticAt ℂ f x}
  constructor
  · exact isOpen_analyticAt ℂ f
  · constructor
    · simpa
    · intro z hz
      simp at hz
      exact differentiableAt hz


theorem HolomorphicAt.contDiffAt
  [CompleteSpace F]
  {f : ℂ → F}
  {z : ℂ}
  {n : ℕ}
  (hf : HolomorphicAt f z) :
  ContDiffAt ℝ n f z := by

  let t := {x | HolomorphicAt f x}
  have ht : IsOpen t := HolomorphicAt_isOpen f
  have hz : z ∈ t := by exact hf

  -- ContDiffAt ℝ _ f z
  apply ContDiffOn.contDiffAt _ ((IsOpen.mem_nhds_iff ht).2 hz)
  suffices h : ContDiffOn ℂ n f t from by
    apply ContDiffOn.restrict_scalars ℝ h
  apply DifferentiableOn.contDiffOn _ ht
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  -- DifferentiableAt ℂ f w
  let hfw : HolomorphicAt f w := hw
  obtain ⟨s, _, h₂s, h₃s⟩ := HolomorphicAt_iff.1 hfw
  exact h₃s w h₂s


theorem HolomorphicAt.differentiableAt
  {f : ℂ → F}
  {z : ℂ}
  (hf : HolomorphicAt f z) :
  DifferentiableAt ℂ f z := by
  obtain ⟨s, _, h₂s, h₃s⟩ := HolomorphicAt_iff.1 hf
  exact h₃s z h₂s


theorem HolomorphicAt.CauchyRiemannAt
  {f : ℂ → F}
  {z : ℂ}
  (h : HolomorphicAt f z) :
  partialDeriv ℝ Complex.I f =ᶠ[nhds z] Complex.I • partialDeriv ℝ 1 f := by

  obtain ⟨s, h₁s, hz, h₂f⟩ := HolomorphicAt_iff.1 h

  apply Filter.eventuallyEq_iff_exists_mem.2
  use s
  constructor
  · exact IsOpen.mem_nhds h₁s hz
  · intro w hw
    let h := h₂f w hw
    unfold partialDeriv
    apply CauchyRiemann₅ h
