import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem

open Function MeromorphicOn Metric Real Set Classical ValueDistribution


lemma characteristic_sub_characteristic_inv {a : ℂ} {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) :
    0  = logCounting f a := by

  have R : ℝ := by sorry
  have hR : R ≠ 0 := by sorry
  have h₁f : MeromorphicOn f (closedBall 0 |R|) := by tauto


  have jensen := MeromorphicOn.circleAverage_log_norm hR h₁f
  simp at jensen

  unfold logCounting
  unfold locallyFinsuppWithin.logCounting
  simp


  sorry
