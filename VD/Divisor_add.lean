import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalFormAt
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import VD.mathlibAddOn

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {z₀ : 𝕜} {U : Set 𝕜}


/-- A function that is analytic in a neighborhood of `U` is meromorphic on `U`. -/
theorem AnalyticOnNhd.MeromorphicOn (hf : AnalyticOnNhd 𝕜 f U) :
    MeromorphicOn f U := fun x hx ↦ (hf x hx).meromorphicAt

/-- Analytic functions have non-negative divisors. -/
theorem AnalyticOnNhd.divisor_nonneg [CompleteSpace E] (hf : AnalyticOnNhd 𝕜 f U) :
    0 ≤ MeromorphicOn.divisor f U := by
  intro x
  by_cases hx : x ∈ U
  · simp [hf.MeromorphicOn, hx, (hf x hx).meromorphicAt_order_nonneg]
  simp [hx]

/-- Adding an analytic function to a meromorphic one does not change the pole divisor. -/
theorem MeromorphicOn.divisor_add_analytic [CompleteSpace E] (hf : MeromorphicOn f U)
    (hg : AnalyticOnNhd 𝕜 g U) :
    (divisor f U)⁻ = (divisor (f + g) U)⁻ := by
  ext x
  by_cases hx : x ∈ U
  · simp [negPart_def, hx, hf, hf.add hg.meromorphicOn]
    rcases (inf_le_iff.1 ((hf x hx).order_add (hg x hx).meromorphicAt)) with h | h
    · sorry
    · sorry
  simp [hx]


namespace MeromorphicOn

theorem xx [CompleteSpace E] (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    min (divisor f U) (divisor g U) ≤ divisor (f + g) U := by
  intro x
  by_cases hx : x ∈ U
  · simp only [Function.locallyFinsuppWithin.min_apply, hf, hx, divisor_apply, hg, hf.add hg]
    by_cases h₂f : (hf x hx).order = ⊤
    · simp only [h₂f, WithTop.untop₀_top, inf_le_iff]
      right
      apply le_of_eq
      congr 1
      rw [eq_comm, ((hf x hx).add (hg x hx)).order_congr]
      filter_upwards [(hf x hx).order_eq_top_iff.1 h₂f]
      simp
    by_cases h₂g : (hg x hx).order = ⊤
    · simp [h₂g, WithTop.untop₀_top, inf_le_iff]
      left
      apply le_of_eq
      congr 1
      rw [eq_comm, ((hf x hx).add (hg x hx)).order_congr]
      filter_upwards [(hg x hx).order_eq_top_iff.1 h₂g]
      simp

    lift (hf x hx).order to ℤ using h₂f with n hn
    lift (hg x hx).order to ℤ using h₂g with m hm

    have := (hf x hx).order_add (hg x hx)

    simp
    simp_all

    sorry
  simp [hx]


end MeromorphicOn
