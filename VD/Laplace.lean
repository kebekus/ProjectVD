import Mathlib.Analysis.Complex.Basic
import VD.partialDeriv

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

noncomputable def Complex.laplace (f : ℂ → F) : ℂ → F :=
  partialDeriv ℝ 1 (partialDeriv ℝ 1 f) + partialDeriv ℝ Complex.I (partialDeriv ℝ Complex.I f)

notation "Δ" => Complex.laplace

variable {f f₁ f₂ : ℂ → F} {x : ℂ}

theorem laplace_eventuallyEq' (h : f₁ =ᶠ[nhds x] f₂) : Δ f₁ =ᶠ[nhds x] Δ f₂ := by
  unfold Complex.laplace
  apply Filter.EventuallyEq.add
  exact partialDeriv_eventuallyEq' ℝ (partialDeriv_eventuallyEq' ℝ h 1) 1
  exact partialDeriv_eventuallyEq' ℝ (partialDeriv_eventuallyEq' ℝ h Complex.I) Complex.I

theorem laplace_eventuallyEq (h : f₁ =ᶠ[nhds x] f₂) : Δ f₁ x = Δ f₂ x := by
  apply Filter.EventuallyEq.eq_of_nhds
  exact laplace_eventuallyEq' h

lemma ContDiffOn.differentiableAt_partialDeriv {s : Set ℂ} (hs : IsOpen s) {x y : ℂ} (hy : y ∈ s) (hf: ContDiffOn ℝ 2 f s) :
      DifferentiableAt ℝ (partialDeriv ℝ x f) y := by
  apply ContDiffAt.differentiableAt
  · exact (partialDeriv_contDiffAt _ ((hf _ hy).contDiffAt (hs.mem_nhds hy)) x)
  · apply le_refl

lemma ContDiffOn.differentiableAt {s : Set ℂ} (hs : IsOpen s)
    (h : ContDiffOn ℝ 2 f s) (hx : x ∈ s) : DifferentiableAt ℝ f x :=
  (h.differentiableOn one_le_two).differentiableAt (hs.mem_nhds hx)

lemma partialDeriv_add_eventually_equal (y : ℂ) {s : Set ℂ} (hs : IsOpen s) (hx : x ∈ s)
    (h₁ : ContDiffOn ℝ 2 f₁ s) (h₂ : ContDiffOn ℝ 2 f₂ s)  :
    partialDeriv ℝ y (f₁ + f₂) =ᶠ[nhds x] (partialDeriv ℝ y f₁) + (partialDeriv ℝ y f₂) := by
  apply Filter.eventuallyEq_iff_exists_mem.2
  use s, hs.mem_nhds hx
  intro z hz
  apply partialDeriv_add₂_differentiableAt
  apply h₁.differentiableAt hs hz
  exact h₂.differentiableAt hs hz

theorem laplace_add_ContDiffOn {s : Set ℂ} (hs : IsOpen s)
    (h₁ : ContDiffOn ℝ 2 f₁ s) (h₂ : ContDiffOn ℝ 2 f₂ s) (hx : x ∈ s) :
  Δ (f₁ + f₂) x = (Δ f₁) x + (Δ f₂) x := by
  have hf₃ : partialDeriv ℝ 1 (f₁ + f₂) =ᶠ[nhds x] (partialDeriv ℝ 1 f₁) + (partialDeriv ℝ 1 f₂) := by
    apply partialDeriv_add_eventually_equal 1 hs hx h₁ h₂
  have hf₄ : partialDeriv ℝ Complex.I (f₁ + f₂) =ᶠ[nhds x] (partialDeriv ℝ Complex.I f₁) + (partialDeriv ℝ Complex.I f₂) := by
    apply partialDeriv_add_eventually_equal Complex.I hs hx h₁ h₂
  unfold Complex.laplace
  simp
  rw [partialDeriv_eventuallyEq ℝ hf₃]
  rw [partialDeriv_add₂_differentiableAt ℝ (h₁.differentiableAt_partialDeriv hs hx) (h₂.differentiableAt_partialDeriv hs hx)]
  rw [partialDeriv_eventuallyEq ℝ hf₄]
  rw [partialDeriv_add₂_differentiableAt ℝ (h₁.differentiableAt_partialDeriv hs hx) (h₂.differentiableAt_partialDeriv hs hx)]
  abel
  -- I am super confused at this point because the tactic 'ring' does not work.
  -- I do not understand why. So, I need to do things by hand.

theorem laplace_add (h₁ : ContDiff ℝ 2 f₁) (h₂ : ContDiff ℝ 2 f₂) :
    Δ (f₁ + f₂) = (Δ f₁) + (Δ f₂) := by
  ext x
  apply laplace_add_ContDiffOn isOpen_univ h₁.contDiffOn h₂.contDiffOn trivial

lemma ContDiffAt.contDiffOn_nbd {f : ℂ → F} {x : ℂ} (h : ContDiffAt ℝ 2 f x) :
    ∃ s ∈ nhds x, ContDiffOn ℝ 2 f s := by
  apply ContDiffAt.contDiffOn h (le_refl 2)
  simp

lemma ContDiffAt.contDiffOn_open {f : ℂ → F} {x : ℂ} (h : ContDiffAt ℝ 2 f x) :
    ∃ s, IsOpen s ∧ x ∈ s ∧ ContDiffOn ℝ 2 f s := by
  obtain ⟨s, hx, hf⟩ := h.contDiffOn_nbd
  obtain ⟨U, hU⟩ := mem_nhds_iff.1 hx
  use U
  exact ⟨hU.2.1, hU.2.2, hf.mono hU.1⟩

theorem laplace_add_ContDiffAt (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) x = (Δ f₁) x + (Δ f₂) x := by
  obtain ⟨s₁, hs₁, hx₁, hf₁⟩ := h₁.contDiffOn_open
  obtain ⟨s₂, hs₂, hx₂, hf₂⟩ := h₂.contDiffOn_open
  exact laplace_add_ContDiffOn (IsOpen.inter hs₁ hs₂)
    (hf₁.mono Set.inter_subset_left) (hf₂.mono Set.inter_subset_right) (Set.mem_inter hx₁ hx₂)

theorem laplace_add_ContDiffAt' (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) =ᶠ[nhds x] (Δ f₁) + (Δ f₂):= by
  obtain ⟨s₁, hs₁, hx₁, hf₁⟩ := h₁.contDiffOn_open
  obtain ⟨s₂, hs₂, hx₂, hf₂⟩ := h₂.contDiffOn_open
  have h₁ : s₁ ∈ nhds x := by exact IsOpen.mem_nhds hs₁ hx₁
  have h₂ : s₂ ∈ nhds x := by exact IsOpen.mem_nhds hs₂ hx₂
  apply Filter.eventuallyEq_of_mem (Filter.inter_mem h₁ h₂)
  intro y hy
  apply laplace_add_ContDiffAt
  have : s₁ ∈ nhds y := IsOpen.mem_nhds hs₁ (Set.mem_of_mem_inter_left hy)
  apply hf₁.contDiffAt this
  have : s₂ ∈ nhds y := IsOpen.mem_nhds hs₂ (Set.mem_of_mem_inter_right hy)
  apply hf₂.contDiffAt this

theorem laplace_smul {f : ℂ → F} : ∀ v : ℝ, Δ (v • f) = v • (Δ f) := by
  intro v
  unfold Complex.laplace
  simp [partialDeriv_smul₂]

theorem laplace_compCLMAt {f : ℂ → F} {l : F →L[ℝ] G} {x : ℂ} (h : ContDiffAt ℝ 2 f x) :
    Δ (l ∘ f) x = (l ∘ (Δ f)) x := by
  obtain ⟨v, hv₁, hv₂, hv₃, hv₄⟩ : ∃ v ∈ nhds x, (IsOpen v) ∧ (x ∈ v) ∧ (ContDiffOn ℝ 2 f v) := by
    obtain ⟨u, hu₁, hu₂⟩ : ∃ u ∈ nhds x, ContDiffOn ℝ 2 f u := by
      apply ContDiffAt.contDiffOn h
      rfl
      simp
    obtain ⟨v, hv₁, hv₂, hv₃⟩ := mem_nhds_iff.1 hu₁
    use v, hv₂.mem_nhds hv₃, hv₂, hv₃
    exact hu₂.congr_mono (fun x => congrFun rfl) hv₁
  have D (w : ℂ) : partialDeriv ℝ w (l ∘ f) =ᶠ[nhds x] l ∘ partialDeriv ℝ w (f) := by
    apply Filter.eventuallyEq_iff_exists_mem.2
    use v, hv₂.mem_nhds hv₃
    intro y hy
    apply partialDeriv_compContLinAt
    apply (hv₄.differentiableOn one_le_two).differentiableAt (hv₂.mem_nhds hy)
  unfold Complex.laplace
  simp
  rw [partialDeriv_eventuallyEq ℝ (D 1) 1]
  rw [partialDeriv_compContLinAt]
  rw [partialDeriv_eventuallyEq ℝ (D Complex.I) Complex.I]
  rw [partialDeriv_compContLinAt]
  simp
  -- DifferentiableAt ℝ (partialDeriv ℝ Complex.I f) x
  apply ContDiffAt.differentiableAt (partialDeriv_contDiffAt ℝ (ContDiffOn.contDiffAt hv₄ hv₁) Complex.I) le_rfl
  -- DifferentiableAt ℝ (partialDeriv ℝ 1 f) x
  apply ContDiffAt.differentiableAt (partialDeriv_contDiffAt ℝ (ContDiffOn.contDiffAt hv₄ hv₁) 1) le_rfl

theorem laplace_compCLM {f : ℂ → F} {l : F →L[ℝ] G} (h : ContDiff ℝ 2 f) :
    Δ (l ∘ f) = l ∘ (Δ f) := by
  funext z
  exact laplace_compCLMAt h.contDiffAt

theorem laplace_compCLE {f : ℂ → F} {l : F ≃L[ℝ] G} :
  Δ (l ∘ f) = l ∘ (Δ f) := by
  unfold Complex.laplace
  simp [partialDeriv_compCLE]
