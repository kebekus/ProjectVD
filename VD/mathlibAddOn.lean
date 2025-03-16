import Mathlib.Analysis.Analytic.IsolatedZeros
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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}

open Topology Filter

/-- Two analytic functions agree on a punctured neighborhood iff they agree on a neighborhood. -/
/-
theorem AnalyticAt.eventuallyEq_nhd_iff_eventuallyEq_nhdNE (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
  f =ᶠ[𝓝[≠] z₀] g ↔ f =ᶠ[𝓝 z₀] g := by
  constructor <;> intro hfg
  · rcases ((hf.sub hg).eventually_eq_zero_or_eventually_ne_zero) with h | h
    · exact Filter.eventuallyEq_iff_sub.2 h
    · simpa using (Filter.eventually_and.2 ⟨Filter.eventuallyEq_iff_sub.mp hfg, h⟩).exists
  · exact hfg.filter_mono nhdsWithin_le_nhds
-/

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
