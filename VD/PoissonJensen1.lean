import VD.PoissonJensen0

open Complex Filter Function MeromorphicOn Metric Real Set Classical Topology --ValueDistribution

/-!
## Additional Material
-/


/-!
## Formula goes here
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {x c w : ℂ} {f h : ℂ → ℂ}


theorem poissonJensen {c : ℂ}
    (h₁w : w ∈ ball c R)
    (h₃w : meromorphicOrderAt f w = 0)
    (h₁f : MeromorphicOn f (closedBall c R))
    (h₂f : ∀ u : (closedBall (c : ℂ) R), meromorphicOrderAt f u ≠ ⊤) -- can be deduced
    (hR : 0 < R) : -- can be decuced
    Real.log ‖meromorphicTrailingCoeffAt f w‖
      = circleAverage (re ∘ herglotzRieszKernel c w * (Real.log ‖f ·‖)) c R
        - ∑ᶠ i, (divisor f (ball c R) i) * Real.log ‖canonicalFactor R (i - c) w‖ := by
  let g := fun z ↦ f (z + c)
  have : f = fun z ↦ g (z - c) := by simp [g]
  repeat rw [this]
  simp
  have : meromorphicTrailingCoeffAt (fun z ↦ g (z - c)) w = meromorphicTrailingCoeffAt g (w - c) := by
    sorry
  rw [this]
  rw [poissonJensen₀ (R := R)]
  congr 1
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
