import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalAverage
import VD.ToMathlib.codiscreteWithin

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

/-- Interval averages are invariant when functions change along discrete sets. -/
theorem intervalAverage_congr_codiscreteWithin {a b : ℝ} {f₁ f₂ : ℝ → ℝ}
    (hf : f₁ =ᶠ[codiscreteWithin (Ι a b)] f₂) :
    ⨍ (x : ℝ) in a..b, f₁ x = ⨍ (x : ℝ) in a..b, f₂ x := by
  rw [interval_average_eq, intervalIntegral.integral_congr_codiscreteWithin hf,
    ← interval_average_eq]
