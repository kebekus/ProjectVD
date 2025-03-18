import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.SpecialFunctions.Exp

open Topology Filter

theorem continousAt_ne_iff_eventually_ne
    {X : Type*} [TopologicalSpace X] {z₀ : X}
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : X → Y}
    (hf : ContinuousAt f z₀) (hg : ContinuousAt g z₀) :
    f z₀ ≠ g z₀ ↔ ∀ᶠ x in 𝓝 z₀, f x ≠ g x := by
  constructor <;> intro hfg
  · obtain ⟨Uf, Ug, h₁U, h₂U, h₃U, h₄U, h₅U⟩ := t2_separation hfg
    rw [Set.disjoint_iff_inter_eq_empty] at h₅U
    filter_upwards [inter_mem
      (hf.preimage_mem_nhds (IsOpen.mem_nhds h₁U h₃U))
      (hg.preimage_mem_nhds (IsOpen.mem_nhds h₂U h₄U))]
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
    by_contra H
    rw [H] at hx
    have : g x ∈ Uf ∩ Ug := hx
    simp [h₅U] at this
  · obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 hfg
    exact h₁t z₀ h₃t

theorem ContinousAt.eventuallyEq_nhd_iff_eventuallyEq_nhdNE
    {X : Type*} [TopologicalSpace X] {z₀ : X}
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : X → Y}
    (hf : ContinuousAt f z₀) (hg : ContinuousAt g z₀) (h : Filter.NeBot (𝓝[≠] z₀)) :
  f =ᶠ[𝓝[≠] z₀] g ↔ f =ᶠ[𝓝 z₀] g := by
  constructor <;> intro hfg
  · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE hfg
    by_contra hCon
    have : {x | f x ≠ g x ∧ f x = g x} ≠ ∅ := by
      have h₁ := (eventually_nhdsWithin_of_eventually_nhds
        ((continousAt_ne_iff_eventually_ne hf hg).1 hCon)).and hfg
      have h₂ : ∅ ∉ 𝓝[≠] z₀ := by exact empty_not_mem (𝓝[≠] z₀)
      rw [Filter.neBot_iff] at h
      by_contra H
      rw [Filter.Eventually, H] at h₁
      tauto
    rw [← Set.nonempty_iff_ne_empty] at this
    obtain ⟨a, ha⟩ := this
    simp at ha
  · exact hfg.filter_mono nhdsWithin_le_nhds


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
variable {f f₀ f₁ g : E → F}
variable {f' f₀' f₁' g' : E →L[𝕜] F}
variable (e : E →L[𝕜] F)
variable {x : E}
variable {s t : Set E}
variable {L L₁ L₂ : Filter E}

variable {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]

variable {f g : E → F} {n : ℕ} {z z₀ : 𝕜}


/-- Two analytic functions agree on a punctured neighborhood iff they agree on a neighborhood. -/

theorem ContinousAt.eventuallyEq_nhd_iff_eventuallyEq_nhdNE'
    {f g : 𝕜 → E} {z₀ : 𝕜} [Nontrivial E] [CompleteSpace E]
    (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    f =ᶠ[𝓝[≠] z₀] g ↔ f =ᶠ[𝓝 z₀] g := by
  apply ContinousAt.eventuallyEq_nhd_iff_eventuallyEq_nhdNE
    hf.continuousAt hg.continuousAt (NormedField.nhdsNE_neBot z₀)

variable [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E}

lemma rwx
  {a b : WithTop ℤ}
  (ha : a ≠ ⊤)
  (hb : b ≠ ⊤) :
  a + b ≠ ⊤ := by
  simp; tauto

lemma untop_add
  {a b : WithTop ℤ}
  (ha : a ≠ ⊤)
  (hb : b ≠ ⊤) :
  (a + b).untop (rwx ha hb) = a.untop ha + (b.untop hb) := by
  rw [WithTop.untop_eq_iff]
  rw [WithTop.coe_add]
  rw [WithTop.coe_untop]
  rw [WithTop.coe_untop]

lemma untop'_of_ne_top
  {a : WithTop ℤ}
  {d : ℤ}
  (ha : a ≠ ⊤) :
  WithTop.untopD d a = a := by
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 ha
  rw [← hb]
  simp
