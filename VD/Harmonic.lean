import VD.ToMathlib.Laplace

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

open Topology

theorem laplace_smul_nhd {x : E} {f : E → F} (v : ℝ) (hf : ContDiffAt ℝ 2 f x) :
    Δ (v • f) =ᶠ[𝓝 x] v • (Δ f) := by
  filter_upwards [hf.eventually (not_eq_of_beq_eq_false rfl)] with a ha
  simp [laplace_smul v ha]



def HarmonicAt (f : E → F) (x : E) : Prop := (ContDiffAt ℝ 2 f x) ∧ (Δ f =ᶠ[𝓝 x] 0)

def HarmonicOnNhd (f : E → F) (s : Set E) : Prop := ∀ x ∈ s, HarmonicAt f x

lemma HarmonicOnNhd.mono {f : E → F} {s t : Set E} (h : HarmonicOnNhd f s) (hst : t ⊆ s) :
    HarmonicOnNhd f t := fun x hx ↦ h x (hst hx)

theorem HarmonicAt.eventually {f : E → F} {x : E} (h:  HarmonicAt f x) :
    ∀ᶠ y in 𝓝 x, HarmonicAt f y := by
  filter_upwards [h.1.eventually (not_eq_of_beq_eq_false rfl), h.2.eventually_nhds] with a h₁a h₂a
  exact ⟨h₁a, h₂a⟩

theorem harmonicAt_isOpen (f : E → F) : IsOpen { x : E | HarmonicAt f x } := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact hx.eventually

theorem harmonicAt_congr_nhds {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) :
    HarmonicAt f₁ x ↔ HarmonicAt f₂ x := by
  constructor <;> intro hf
  · exact ⟨hf.1.congr_of_eventuallyEq h.symm, (laplace_congr_nhds h.symm).trans hf.2⟩
  · exact ⟨hf.1.congr_of_eventuallyEq h, (laplace_congr_nhds h).trans hf.2⟩

theorem HarmonicAt.add {f₁ f₂ : E → F} {x : E} (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x) :
    HarmonicAt (f₁ + f₂) x := by
  constructor
  · exact h₁.1.add h₂.1
  · filter_upwards [h₁.1.laplace_add_nhd h₂.1, h₁.2, h₂.2] with a h₁a h₂a h₃a
    simp_all

theorem HarmonicAt.const_smul {f : E → F} {x : E} {c : ℝ} (h : HarmonicAt f x) :
    HarmonicAt (c • f) x := by
  constructor
  · exact h.1.const_smul c
  · filter_upwards [laplace_smul_nhd c h.1, h.2] with a h₁a h₂a
    simp_all

theorem harmonicAt_comp_CLM_is_harmonicAt {f : E → F} {z : E} {l : F →L[ℝ] G}
    (h : HarmonicAt f z) : HarmonicAt (l ∘ f) z := by
  constructor
  · exact h.1.continuousLinearMap_comp l
  · filter_upwards [h.1.laplace_CLM_comp (l := l), h.2] with a h₁a h₂a
    simp_all



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


section harmonicOn

variable {f f₁ f₂ : ℂ → F} {s : Set ℂ} {c : ℝ}

theorem harmonicOn_add_harmonicOn_is_harmonicOn (hs : IsOpen s)
    (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s) :
    HarmonicOnNhd (f₁ + f₂) s := by
  constructor
  · exact h₁.1.add h₂.1
  · intro z hz
    simp [laplace_add_ContDiffOn hs h₁.1 h₂.1 hz, h₁.2 _ hz, h₂.2 _ hz]

theorem harmonicOn_smul_const_is_harmonicOn (_ : IsOpen s) (h : HarmonicOnNhd f s) :
    HarmonicOnNhd (c • f) s := by
  constructor
  · exact h.1.const_smul c
  · intro z hz
    simp [laplace_smul, h.2 z hz]

theorem harmonicOn_iff_smul_const_is_harmonicOn (hs : IsOpen s) (hc : c ≠ 0) :
  HarmonicOnNhd f s ↔ HarmonicOnNhd (c • f) s := by
  constructor
  · exact harmonicOn_smul_const_is_harmonicOn hs
  · nth_rewrite 2 [((eq_inv_smul_iff₀ hc).mpr rfl : f = c⁻¹ • c • f)]
    exact fun a => harmonicOn_smul_const_is_harmonicOn hs a

theorem harmonicOn_comp_CLM_is_harmonicOn {f : ℂ → F₁} {s : Set ℂ} {l : F₁ →L[ℝ] G} (hs : IsOpen s)
    (h : HarmonicOnNhd f s) : HarmonicOnNhd (l ∘ f) s := by
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
    (hs : IsOpen s) : HarmonicOnNhd f s ↔ HarmonicOnNhd (l ∘ f) s := by
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
  apply HarmonicOnNhd_mono h₃s₁ Set.inter_subset_left
  apply HarmonicOnNhd_mono h₃s₂ Set.inter_subset_right

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
