import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.SpecialFunctions.Exp

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




open Topology Filter

lemma eventuallyEq_nhdsWithin_of_eventuallyEq_nhds
  {α τ : Type*}
  {f g : τ → α} [TopologicalSpace τ]
  {z₀ : τ}
  (h₁ : f =ᶠ[𝓝[≠] z₀] g)
  (h₂ : f z₀ = g z₀) :
  f =ᶠ[𝓝 z₀] g := by
  filter_upwards [eventually_nhdsWithin_iff.1 h₁]
  intro x hx
  by_cases h₂x : x = z₀
  · simp [h₂x, h₂]
  · tauto

-- unclear where this should go

lemma WithTopCoe
  {n : WithTop ℕ} :
  WithTop.map (Nat.cast : ℕ → ℤ) n = 0 → n = 0 := by
  rcases n with h|h
  · intro h
    contradiction
  · intro h₁
    simp only [WithTop.map, Option.map] at h₁
    have : (h : ℤ) = 0 := by
      exact WithTop.coe_eq_zero.mp h₁
    have : h = 0 := by
      exact Int.ofNat_eq_zero.mp this
    rw [this]
    rfl

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
