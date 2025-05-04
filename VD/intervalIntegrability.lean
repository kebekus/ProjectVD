import Mathlib.Analysis.Analytic.Linear
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

/- Integral and Integrability up to changes on codiscrete sets -/
theorem integrability_congr_changeDiscrete
    {f₁ f₂ : ℂ → ℝ} {U : Set ℂ} {r : ℝ}
    (hU : Metric.sphere (0 : ℂ) |r| ⊆ U)
    (hR : r ≠ 0)
    (hf : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
  IntervalIntegrable (f₁ ∘ (circleMap 0 r)) MeasureTheory.volume 0 (2 * π) ↔ IntervalIntegrable (f₂ ∘ (circleMap 0 r)) MeasureTheory.volume 0 (2 * π) := by
  constructor
  · apply (intervalIntegrable_congr_codiscreteWithin _).1
    filter_upwards [Filter.codiscreteWithin.mono (by tauto : (Ι 0 (2 * π)) ⊆ Set.univ)
      (circleMap_preimage_codiscrete hR (Filter.codiscreteWithin.mono hU hf))]
    tauto
  · apply (intervalIntegrable_congr_codiscreteWithin _).1
    filter_upwards [Filter.codiscreteWithin.mono (by tauto : (Ι 0 (2 * π)) ⊆ Set.univ)
      (circleMap_preimage_codiscrete hR (Filter.codiscreteWithin.mono hU hf.symm))]
    tauto

theorem integral_congr_changeDiscrete
  {f₁ f₂ : ℂ → ℝ}
  {U : Set ℂ}
  {r : ℝ}
  (hr : r ≠ 0)
  (hU : Metric.sphere 0 |r| ⊆ U)
  (hf : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
  ∫ (x : ℝ) in (0)..(2 * π), f₁ (circleMap 0 r x) = ∫ (x : ℝ) in (0)..(2 * π), f₂ (circleMap 0 r x) := by
  apply intervalIntegral.integral_congr_codiscreteWithin
  filter_upwards [Filter.codiscreteWithin.mono (by tauto : (Ι 0 (2 * π)) ⊆ Set.univ)
    (circleMap_preimage_codiscrete hr (Filter.codiscreteWithin.mono hU hf))]
  tauto

lemma circleMap_neg {r x : ℝ} {c : ℂ} :
    circleMap c (-r) x = circleMap c r (x + π) := by
  simp [circleMap, add_mul, Complex.exp_add]

-- unused
theorem circleIntegrable_congr_negRadius {f : ℂ → ℝ} {r : ℝ} :
  CircleIntegrable f 0 r → CircleIntegrable f 0 (-r) := by
  unfold CircleIntegrable
  intro h
  simp_rw [circleMap_neg]
  have t₀ : (fun θ ↦ f (circleMap 0 r θ)).Periodic (2 * π) := by
    intro x
    simp [periodic_circleMap 0 r x]
  rw [← zero_add (2 * π)] at h
  have := (t₀.intervalIntegrable two_pi_pos h π (3 * π)).comp_add_right π
  simp_all [← (by ring : 3 * π - π = 2 * π)]

theorem integrabl_congr_negRadius
  {f : ℂ → ℝ}
  {r : ℝ} {c : ℂ} :
  ∫ (x : ℝ) in (0)..(2 * π), f (circleMap c r x) = ∫ (x : ℝ) in (0)..(2 * π), f (circleMap c (-r) x) := by

  simp_rw [circleMap_neg]
  have t₀ : Function.Periodic (fun (θ : ℝ) ↦ f (circleMap c r θ)) (2 * π) := by
    intro x
    simp
    congr 1
    exact periodic_circleMap c r x
  have B := intervalIntegral.integral_comp_add_right (a := 0) (b := 2 * π) (fun θ => f (circleMap c r θ)) π
  rw [B]
  let X := t₀.intervalIntegral_add_eq 0 (0 + π)
  simp at X
  rw [X]
  simp
  rw [add_comm]
