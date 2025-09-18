import Mathlib.Analysis.Complex.Harmonic.Analytic

open Complex InnerProductSpace Metric Topology

variable
  {f : ℂ → ℝ} {x : ℂ}

theorem HarmonicAt.analyticAt (hf : HarmonicAt f x) : AnalyticAt ℝ f x := by
  obtain ⟨ε, h₁ε, h₂ε⟩ := isOpen_iff.1 (isOpen_setOf_harmonicAt (f := f)) x hf
  obtain ⟨F, h₁F, h₂F⟩ := harmonic_is_realOfHolomorphic (fun _ hy ↦ h₂ε hy)
  rw [(by aesop : (fun z ↦ (F z).re) = Complex.reCLM ∘ F)] at h₂F
  rw [analyticAt_congr (Filter.eventually_of_mem (ball_mem_nhds x h₁ε) (fun y hy ↦ h₂F.symm hy))]
  exact (reCLM.analyticAt (F x)).comp (h₁F x (mem_ball_self h₁ε)).restrictScalars
