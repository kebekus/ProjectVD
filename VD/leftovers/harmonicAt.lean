import VD.laplace

variable {F G F₁ G₁ : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]

def Harmonic (f : ℂ → F) : Prop := (ContDiff ℝ 2 f) ∧ (∀ z, Δ f z = 0)

def HarmonicAt (f : ℂ → F) (x : ℂ) : Prop := (ContDiffAt ℝ 2 f x) ∧ (Δ f =ᶠ[nhds x] 0)

def HarmonicOn (f : ℂ → F) (s : Set ℂ) : Prop := (ContDiffOn ℝ 2 f s) ∧ (∀ z ∈ s, Δ f z = 0)

lemma Harmonic_iff_HarmonicOn_univ {f : ℂ → F} : Harmonic f ↔ HarmonicOn f Set.univ := by
  constructor <;> intro h
  · constructor
    · exact contDiffOn_univ.mpr h.1
    · simp [h.2]
  · constructor
    · exact contDiffOn_univ.mp h.1
    · simp [h.2]

lemma HarmonicOn_le {f : ℂ → F} {s t : Set ℂ} (h : HarmonicOn f s) (hst : t ⊆ s) :
    HarmonicOn f t := by
  constructor
  · exact h.1.mono hst
  · exact fun z hz => h.2 z (hst hz)

theorem HarmonicAt_iff {f : ℂ → F} {x : ℂ} :
    HarmonicAt f x ↔ ∃ s : Set ℂ, IsOpen s ∧ x ∈ s ∧ HarmonicOn f s := by
  constructor
  · intro hf
    obtain ⟨s₁, h₁s₁, h₂s₁, h₃s₁⟩ := hf.1.contDiffOn' le_rfl (by trivial)
    simp at h₃s₁
    obtain ⟨t₂, h₁t₂, h₂t₂⟩ := (Filter.eventuallyEq_iff_exists_mem.1 hf.2)
    obtain ⟨s₂, h₁s₂, h₂s₂, h₃s₂⟩ := mem_nhds_iff.1 h₁t₂
    use s₁ ∩ s₂, h₁s₁.inter h₂s₂, ⟨h₂s₁, h₃s₂⟩, h₃s₁.mono Set.inter_subset_left
    exact fun z hz ↦ h₂t₂ (h₁s₂ hz.2)
  · intro hyp
    obtain ⟨s, h₁s, h₂s, h₁f, h₂f⟩ := hyp
    constructor
    · apply h₁f.contDiffAt (h₁s.mem_nhds_iff.2 h₂s)
    · apply Filter.eventuallyEq_iff_exists_mem.2
      use s, h₁s.mem_nhds_iff.2 h₂s, h₂f

theorem HarmonicAt_isOpen (f : ℂ → F) : IsOpen { x : ℂ | HarmonicAt f x } := by
  rw [← subset_interior_iff_isOpen]
  intro x hx
  simp at hx
  obtain ⟨s, h₁s, h₂s, h₃s⟩ := HarmonicAt_iff.1 hx
  use s
  constructor
  · simp
    constructor
    · exact h₁s
    · intro x hx
      simp
      rw [HarmonicAt_iff]
      use s
  · exact h₂s

theorem HarmonicAt_eventuallyEq' {f₁ f₂ : ℂ → F} {x : ℂ} (hf : HarmonicAt f₁ x) (h : f₁ =ᶠ[nhds x] f₂) :
    HarmonicAt f₂ x :=
  ⟨hf.1.congr_of_eventuallyEq h.symm, (laplace_eventuallyEq' h.symm).trans hf.2⟩

theorem HarmonicAt_eventuallyEq {f₁ f₂ : ℂ → F} {x : ℂ} (h : f₁ =ᶠ[nhds x] f₂) :
    HarmonicAt f₁ x ↔ HarmonicAt f₂ x := by
  constructor <;> intro hf
  · apply HarmonicAt_eventuallyEq' hf h
  · apply HarmonicAt_eventuallyEq' hf h.symm

theorem HarmonicOn_of_locally_HarmonicOn {f : ℂ → F} {s : Set ℂ}
    (h : ∀ x ∈ s, ∃ (u : Set ℂ), IsOpen u ∧ x ∈ u ∧ HarmonicOn f (s ∩ u)) :
  HarmonicOn f s := by
  constructor
  · apply contDiffOn_of_locally_contDiffOn
    intro x xHyp
    obtain ⟨u, uHyp⟩ := h x xHyp
    use u
    exact ⟨uHyp.1, ⟨uHyp.2.1, uHyp.2.2.1⟩⟩
  · intro x xHyp
    obtain ⟨u, uHyp⟩ := h x xHyp
    exact (uHyp.2.2.2) x ⟨xHyp, uHyp.2.1⟩

theorem HarmonicOn_congr {f₁ f₂ : ℂ → F} {s : Set ℂ} (hs : IsOpen s) (hf₁₂ : ∀ x ∈ s, f₁ x = f₂ x) :
  HarmonicOn f₁ s ↔ HarmonicOn f₂ s := by
  constructor
  · intro h₁
    constructor
    · exact h₁.1.congr (fun x hx ↦ (hf₁₂ x hx).symm)
    · intro z hz
      have : f₁ =ᶠ[nhds z] f₂ := by
        unfold Filter.EventuallyEq
        unfold Filter.Eventually
        simp
        refine mem_nhds_iff.mpr ?_
        use s, hf₁₂, hs, hz
      rw [← laplace_eventuallyEq this]
      exact h₁.2 z hz
  · intro h₁
    constructor
    · exact h₁.1.congr (fun x hx ↦ hf₁₂ x hx)
    · intro z hz
      have : f₁ =ᶠ[nhds z] f₂ := by
        unfold Filter.EventuallyEq
        unfold Filter.Eventually
        simp
        refine mem_nhds_iff.mpr ?_
        use s, hf₁₂, hs, hz
      rw [laplace_eventuallyEq this]
      exact h₁.2 z hz

section harmonicOn

variable {f f₁ f₂ : ℂ → F} {s : Set ℂ} {c : ℝ}

theorem harmonicOn_add_harmonicOn_is_harmonicOn (hs : IsOpen s)
    (h₁ : HarmonicOn f₁ s) (h₂ : HarmonicOn f₂ s) :
    HarmonicOn (f₁ + f₂) s := by
  constructor
  · exact h₁.1.add h₂.1
  · intro z hz
    simp [laplace_add_ContDiffOn hs h₁.1 h₂.1 hz, h₁.2 _ hz, h₂.2 _ hz]

theorem harmonicOn_smul_const_is_harmonicOn (_ : IsOpen s) (h : HarmonicOn f s) :
    HarmonicOn (c • f) s := by
  constructor
  · exact h.1.const_smul c
  · intro z hz
    simp [laplace_smul, h.2 z hz]

theorem harmonicOn_iff_smul_const_is_harmonicOn (hs : IsOpen s) (hc : c ≠ 0) :
  HarmonicOn f s ↔ HarmonicOn (c • f) s := by
  constructor
  · exact harmonicOn_smul_const_is_harmonicOn hs
  · nth_rewrite 2 [((eq_inv_smul_iff₀ hc).mpr rfl : f = c⁻¹ • c • f)]
    exact fun a => harmonicOn_smul_const_is_harmonicOn hs a

theorem harmonicOn_comp_CLM_is_harmonicOn {f : ℂ → F₁} {s : Set ℂ} {l : F₁ →L[ℝ] G} (hs : IsOpen s)
    (h : HarmonicOn f s) : HarmonicOn (l ∘ f) s := by
  constructor
  · -- Continuous differentiability
    apply h.1.continuousLinearMap_comp
  · -- Vanishing of Laplace
    intro z zHyp
    rw [laplace_compCLMAt]
    simp
    rw [h.2 z]
    simp
    assumption
    apply h.1.contDiffAt (hs.mem_nhds zHyp)

theorem harmonicOn_iff_comp_CLE_is_harmonicOn {f : ℂ → F₁} {s : Set ℂ} {l : F₁ ≃L[ℝ] G₁}
    (hs : IsOpen s) : HarmonicOn f s ↔ HarmonicOn (l ∘ f) s := by
  constructor
  · exact harmonicOn_comp_CLM_is_harmonicOn (l := l.toContinuousLinearMap) hs
  · have : f = (l.symm : G₁ →L[ℝ] F₁) ∘ l ∘ f := by
      unfold Function.comp
      simp
    nth_rewrite 2 [this]
    exact harmonicOn_comp_CLM_is_harmonicOn hs
end harmonicOn

section harmonic

variable {f f₁ f₂ : ℂ → F} {s : Set ℂ} {c : ℝ}

theorem harmonic_add_harmonic_is_harmonic (h₁ : Harmonic f₁) (h₂ : Harmonic f₂) :
    Harmonic (f₁ + f₂) := by
  rw [Harmonic_iff_HarmonicOn_univ] at *
  exact harmonicOn_add_harmonicOn_is_harmonicOn isOpen_univ h₁ h₂

theorem harmonic_smul_const_is_harmonic (h : Harmonic f) :
    Harmonic (c • f) := by
  rw [Harmonic_iff_HarmonicOn_univ] at *
  exact harmonicOn_smul_const_is_harmonicOn isOpen_univ h

theorem harmonic_iff_smul_const_is_harmonic (hc : c ≠ 0) :
  Harmonic f ↔ Harmonic (c • f) := by
  repeat rw [Harmonic_iff_HarmonicOn_univ]
  exact harmonicOn_iff_smul_const_is_harmonicOn isOpen_univ hc

theorem harmonic_comp_CLM_is_harmonic {f : ℂ → F₁} {l : F₁ →L[ℝ] G} (h : Harmonic f) :
    Harmonic (l ∘ f) := by
  rw [Harmonic_iff_HarmonicOn_univ] at *
  apply harmonicOn_comp_CLM_is_harmonicOn isOpen_univ h

theorem harmonic_iff_comp_CLE_is_harmonic {f : ℂ → F₁} {l : F₁ ≃L[ℝ] G₁} :
    Harmonic f ↔ Harmonic (l ∘ f) := by
  repeat rw [Harmonic_iff_HarmonicOn_univ]
  exact harmonicOn_iff_comp_CLE_is_harmonicOn isOpen_univ

end harmonic

section harmonicAt

variable {f f₁ f₂ : ℂ → F} {s : Set ℂ} {c : ℝ} {x : ℂ}

theorem harmonicAt_add_harmonicAt_is_harmonicAt
    (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x) : HarmonicAt (f₁ + f₂) x := by
  rw [HarmonicAt_iff] at *
  obtain ⟨s₁, h₁s₁, h₂s₁, h₃s₁⟩ := h₁
  obtain ⟨s₂, h₁s₂, h₂s₂, h₃s₂⟩ := h₂
  use s₁ ∩ s₂
  refine ⟨h₁s₁.inter h₁s₂, Set.mem_inter h₂s₁ h₂s₂, ?_⟩
  apply harmonicOn_add_harmonicOn_is_harmonicOn (h₁s₁.inter h₁s₂)
  apply HarmonicOn_le h₃s₁ Set.inter_subset_left
  apply HarmonicOn_le h₃s₂ Set.inter_subset_right

theorem harmonicAt_smul_const_is_harmonicAt (h : HarmonicAt f x) :
    HarmonicAt (c • f) x := by
  rw [HarmonicAt_iff] at *
  obtain ⟨s, h₁s, h₂s, h₃s⟩ := h
  use s
  refine ⟨h₁s, h₂s, ?_⟩
  apply harmonicOn_smul_const_is_harmonicOn h₁s h₃s

theorem harmonicAt_iff_smul_const_is_harmonicAt (hc : c ≠ 0) :
  HarmonicAt f x ↔ HarmonicAt (c • f) x := by
  constructor
  · exact harmonicAt_smul_const_is_harmonicAt
  · nth_rewrite 2 [((eq_inv_smul_iff₀ hc).mpr rfl : f = c⁻¹ • c • f)]
    exact fun a => harmonicAt_smul_const_is_harmonicAt a

theorem harmonicAt_comp_CLM_is_harmonicAt {f : ℂ → F₁} {z : ℂ} {l : F₁ →L[ℝ] G}
    (h : HarmonicAt f z) : HarmonicAt (l ∘ f) z := by
  rw [HarmonicAt_iff] at *
  obtain ⟨s, h₁s, h₂s, h₃s⟩ := h
  use s
  refine ⟨h₁s, h₂s, ?_⟩
  apply harmonicOn_comp_CLM_is_harmonicOn h₁s h₃s

theorem harmonicAt_iff_comp_CLE_is_harmonicAt {f : ℂ → F₁} {z : ℂ} {l : F₁ ≃L[ℝ] G₁} :
  HarmonicAt f z ↔ HarmonicAt (l ∘ f) z := by
  constructor
  · have : l ∘ f = (l : F₁ →L[ℝ] G₁) ∘ f := by rfl
    rw [this]
    exact harmonicAt_comp_CLM_is_harmonicAt
  · have : f = (l.symm : G₁ →L[ℝ] F₁) ∘ l ∘ f := by
      unfold Function.comp
      simp
    nth_rewrite 2 [this]
    exact harmonicAt_comp_CLM_is_harmonicAt

end harmonicAt
