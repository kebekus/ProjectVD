import VD.ToMathlib.Nevanlinna_mul

open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}


/-- Circle averages commute with addition. -/
theorem circleAverage_add_fun {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℂ} (hf₁ : CircleIntegrable f₁ c R)
    (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (fun z ↦ f₁ z + f₂ z) c R = circleAverage f₁ c R + circleAverage f₂ c R :=
  circleAverage_add hf₁ hf₂

namespace Function.locallyFinsuppWithin

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*} [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]

end Function.locallyFinsuppWithin

namespace ValueDistribution

variable [ProperSpace 𝕜]

theorem proximity_top_add_le {f₁ f₂ : ℂ → ℂ} (h₁f₁ : MeromorphicOn f₁ Set.univ)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) :
    proximity (f₁ + f₂) ⊤ ≤ (proximity f₁ ⊤) + (proximity f₂ ⊤) + (fun _ ↦ log 2) := by
  simp only [proximity, reduceDIte, Pi.add_apply]
  intro r
  have h₂f₁ : MeromorphicOn f₁ (sphere 0 |r|) := fun x _ ↦ h₁f₁ x trivial
  have h₂f₂ : MeromorphicOn f₂ (sphere 0 |r|) := fun x _ ↦ h₁f₂ x trivial
  have h₃f₁ := circleIntegrable_posLog_norm_meromorphicOn h₂f₁
  have h₃f₂ := circleIntegrable_posLog_norm_meromorphicOn h₂f₂
  calc circleAverage (fun x ↦ log⁺ ‖f₁ x + f₂ x‖) 0 r
  _ ≤ circleAverage (fun x ↦ log⁺ ‖f₁ x‖ + log⁺ ‖f₂ x‖ + log 2) 0 r :=
    circleAverage_mono (circleIntegrable_posLog_norm_meromorphicOn (fun_add h₂f₁ h₂f₂))
      ((h₃f₁.add h₃f₂).add (circleIntegrable_const (log 2) 0 r))
      fun x _ ↦ posLog_norm_add_le (f₁ x) (f₂ x)
  _ = circleAverage (log⁺ ‖f₁ ·‖) 0 r + circleAverage (log⁺ ‖f₂ ·‖) 0 r + log 2 := by
    rw [← circleAverage_add h₃f₁ h₃f₂, ← circleAverage_const (log 2),
      ← circleAverage_add (h₃f₁.add h₃f₂) (circleIntegrable_const (log 2) 0 r)]
    congr 1
    ext
    simp [circleAverage_const]

end ValueDistribution
