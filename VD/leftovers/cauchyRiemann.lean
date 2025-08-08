import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Complex.RealDeriv
import VD.partialDeriv

section

variable {z : ℂ} {f : ℂ → ℂ}

lemma ContinuousLinearMap.comp_lineDeriv (w : ℂ) (l : ℂ →L[ℝ] ℝ) (h : DifferentiableAt ℂ f z) :
    lineDeriv ℝ (l ∘ f) z w = l ((fderiv ℝ f z) w) := by
  rw [DifferentiableAt.lineDeriv_eq_fderiv _, fderiv_comp _ (by fun_prop) (h.restrictScalars _)]
  simp
  apply (l.differentiableAt).comp
  exact h.restrictScalars ℝ

end

section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F} {z : ℂ}

theorem CauchyRiemann₅ (h : DifferentiableAt ℂ f z) :
    partialDeriv ℝ Complex.I f z = Complex.I • partialDeriv ℝ 1 f z := by
  unfold partialDeriv
  simp [DifferentiableAt.fderiv_restrictScalars ℝ h]

theorem CauchyRiemann₄ (h : Differentiable ℂ f) :
    partialDeriv ℝ Complex.I f = Complex.I • partialDeriv ℝ 1 f := by
  ext z
  exact CauchyRiemann₅ (h z)

end

section

variable {z : ℂ} {f : ℂ → ℂ}

theorem CauchyRiemann₁ (h : DifferentiableAt ℂ f z) :
    (fderiv ℝ f z) Complex.I = Complex.I * (fderiv ℝ f z) 1 := by
  have := CauchyRiemann₅ h
  unfold partialDeriv at this
  simp [this]

theorem CauchyRiemann₂ (h : DifferentiableAt ℂ f z) :
    lineDeriv ℝ f z Complex.I = Complex.I * lineDeriv ℝ f z 1 := by
  repeat rw [DifferentiableAt.lineDeriv_eq_fderiv (h.restrictScalars ℝ)]
  exact CauchyRiemann₁ h

theorem CauchyRiemann₃ (h : DifferentiableAt ℂ f z) :
    (lineDeriv ℝ (Complex.reCLM ∘ f) z 1 = lineDeriv ℝ (Complex.imCLM ∘ f) z Complex.I)
    ∧ (lineDeriv ℝ (Complex.reCLM ∘ f) z Complex.I = -lineDeriv ℝ (Complex.imCLM ∘ f) z 1) := by
  repeat rw [ContinuousLinearMap.comp_lineDeriv _ _ h]
  simp [CauchyRiemann₁ h, Complex.I_mul]

end
