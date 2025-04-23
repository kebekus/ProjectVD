import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import VD.mathlibAddOn
import VD.ToMathlib.MeromorphicAt_order

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → 𝕜} {z₀ : 𝕜}

-- TODO: AnalyticAt is a codiscrete property within MeromorphicAt

theorem meromorphicAt_congr'
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → E} {x : 𝕜}
  (h : f =ᶠ[𝓝 x] g) : MeromorphicAt f x ↔ MeromorphicAt g x :=
  MeromorphicAt.meromorphicAt_congr (Filter.EventuallyEq.filter_mono h nhdsWithin_le_nhds)

-- Might want to think about adding an analytic function instead of a constant
theorem MeromorphicAt.order_add_const
  --have {z : ℂ} : 0 < (hf z trivial).order → (hf z trivial).order = ((hf.add (MeromorphicOn.const a)) z trivial).order:= by
  {f : ℂ → ℂ}
  {z a : ℂ}
  (hf : MeromorphicAt f z) :
  hf.order < 0 → hf.order = (hf.add (MeromorphicAt.const a z)).order := by
  intro h

  by_cases ha: a = 0
  · -- might want theorem MeromorphicAt.order_const
    have : (MeromorphicAt.const a z).order = ⊤ := by
      rw [MeromorphicAt.order_eq_top_iff]
      rw [ha]
      simp
    rw [hf.order_add_of_unequal_order (MeromorphicAt.const a z)]
    rw [this]
    simp
    rw [this]
    exact h.ne_top
  · have : (MeromorphicAt.const a z).order = (0 : ℤ) := by
      rw [MeromorphicAt.order_eq_int_iff]
      use fun _ ↦ a
      exact ⟨analyticAt_const, by simpa⟩
    rw [hf.order_add_of_unequal_order (MeromorphicAt.const a z)]
    rw [this]
    simp [h.le]
    rw [this]
    exact h.ne
