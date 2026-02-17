import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Harmonic.Analytic

open Asymptotics Classical Complex ComplexConjugate Filter Function Metric Real Set Classical Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}

/-
A real-valued, bounded harmonic function on the complex plane is constant,
assuming every such function is the real part of a holomorphic function.
-/
def Harmonic (u : ℂ → ℝ) : Prop := ∀ z, InnerProductSpace.HarmonicAt u z

theorem bounded_harmonic_on_complex_plane_is_constant
    (assumption : ∀ u : ℂ → ℝ, Harmonic u → ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ z, (f z).re = u z)
    (f : ℂ → ℝ)
    (h_harm : Harmonic f)
    (h_bound : Bornology.IsBounded (range f)) :
    ∀ z w, f z = f w := by
  -- By assumption, there exists a holomorphic function $f$ such that $\Re(f) = u$.
  obtain ⟨F, hF_diff, hF_re⟩ := assumption f h_harm;
  -- Since $g(z)$ is bounded, by Liouville's theorem, $g(z)$ is constant.
  have hg_const : ∀ z w, Complex.exp (F z) = Complex.exp (F w) := by
    apply (differentiable_exp.comp hF_diff).apply_eq_apply_of_bounded
    rw [isBounded_iff_forall_norm_le] at *
    obtain ⟨M, hM⟩ := h_bound
    use exp M
    simp_all only [mem_range, norm_eq_abs, forall_exists_index,
      forall_apply_eq_imp_iff, comp_apply, norm_exp, exp_le_exp]
    grind
  simp_rw [exp_eq_exp_iff_exists_int] at hg_const
  simp only [Complex.ext_iff, add_re, mul_re, intCast_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
    mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, intCast_im,
    add_im, exists_and_left] at hg_const
  grind
