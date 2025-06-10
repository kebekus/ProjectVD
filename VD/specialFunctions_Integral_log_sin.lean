import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import VD.ToMathlib.meromorphicOn_integrability
import Mathlib.Analysis.Complex.CauchyIntegral

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

-- 150 lines max

theorem analyticOnNhd_cos :
    AnalyticOnNhd ℝ Real.cos Set.univ := by
  apply analyticOnNhd_realPart (f := Complex.cos)
  apply Complex.analyticOnNhd_univ_iff_differentiable.mpr
  exact Complex.differentiable_cos

/--
The set where an analytic function has zero or infinite order is discrete within
its domain of analyticity.
-/
theorem AnalyticOnNhd.codiscreteWithin_setOf_analyticOrderAt_eq_zero_or_top {f : ℝ → ℝ} {U : Set ℝ}
    (hf : AnalyticOnNhd ℝ f U) :
    {u : ℝ | analyticOrderAt f u = 0 ∨ analyticOrderAt f u = ⊤} ∈ Filter.codiscreteWithin U := by
  simp_rw [mem_codiscreteWithin, Filter.disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp [analyticOrderAt_eq_top, ha]
  · filter_upwards [h₁f] with a ha
    simp +contextual [(hf a _).analyticOrderAt_eq_zero, ha]

lemma AnalyticOnNhd.xx {x : ℝ} {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f Set.univ) (h₂f : f x ≠ 0) :
    f ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ := by
  filter_upwards [hf.codiscreteWithin_setOf_analyticOrderAt_eq_zero_or_top] with a
  rw [← (hf x trivial).analyticOrderAt_eq_zero] at h₂f
  have {u : ℝ} : analyticOrderAt f u ≠ ⊤ := by
    apply (hf.exists_analyticOrderAt_ne_top_iff_forall (by exact isConnected_univ)).1 _ ⟨u, trivial⟩
    use ⟨x, trivial⟩
    simp_all
  simp only [Set.mem_univ, (hf a _).analyticOrderAt_eq_zero, ne_eq, Set.preimage_compl,
    Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
  tauto

lemma log_sin_eventuallyEq :
    (fun y ↦ log (sin y)) =ᶠ[Filter.codiscrete ℝ] fun y ↦ log (sin (2 * y)) - log 2 - log (cos y) := by
  have t₀ : sin ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ := by
    apply analyticOnNhd_sin.xx (x := π / 2)
    simp
  have t₁ : cos ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ := by
    apply analyticOnNhd_cos.xx (x := 0)
    simp
  filter_upwards [t₀, t₁] with y h₁y h₂y
  simp_all only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
    sin_two_mul, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, or_self, not_false_eq_true, log_mul]
  ring

lemma integral_log_sin₀ : ∫ x in (0)..π, log (sin x) = 2 * ∫ x in (0)..(π / 2), log (sin x) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := π / 2) (c := π)
    (by apply intervalIntegrable_log_sin) (by apply intervalIntegrable_log_sin)]
  conv =>
    left; right; arg 1
    intro x
    rw [← sin_pi_sub]
  rw [intervalIntegral.integral_comp_sub_left (fun x ↦ log (sin x)), sub_self,
    (by linarith : π - π / 2 = π / 2)]
  ring!

lemma integral_log_sin_eq_integral_log_cos :
    ∫ x in (0)..(π / 2), log (sin x) = ∫ x in (0)..(π / 2), log (cos x) := by
  conv =>
    right; arg 1
    intro x
    rw [← sin_pi_div_two_sub]
  simp [intervalIntegral.integral_comp_sub_left (fun x ↦ log (sin x)) (π / 2)]

lemma integral_log_sin₁ : ∫ x in (0)..(π / 2), log (sin x) = -log 2 * π / 2 := by
  calc ∫ x in (0)..(π / 2), log (sin x)
    _ = (∫ x in (0)..(π / 2), log (sin (2 * x))) - π / 2 * log 2 - ∫ x in (0)..(π / 2), log (cos x) := by
      rw [intervalIntegral.integral_congr_codiscreteWithin
        (Filter.codiscreteWithin.mono (by tauto : Ι 0 (π / 2) ⊆ Set.univ) log_sin_eventuallyEq),
        intervalIntegral.integral_sub _ _,
        intervalIntegral.integral_sub _ intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp
      · simpa using (intervalIntegrable_log_sin (a := 0) (b := π)).comp_mul_left 2
      · apply IntervalIntegrable.sub _ intervalIntegrable_const
        simpa using (intervalIntegrable_log_sin (a := 0) (b := π)).comp_mul_left 2
      · exact intervalIntegrable_log_cos
    _ = -log 2 * π / 2 := by
      simp only [intervalIntegral.integral_comp_mul_left (f := fun x ↦ log (sin x)) two_ne_zero,
        mul_zero, (by linarith : 2 * (π / 2) = π), integral_log_sin₀, smul_eq_mul, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel_left₀, ←
        integral_log_sin_eq_integral_log_cos, sub_sub_cancel_left, neg_mul]
      linarith

lemma integral_log_sin₂ : ∫ x in (0)..π, log (sin x) = -log 2 * π := by
  rw [integral_log_sin₀, integral_log_sin₁]
  ring
