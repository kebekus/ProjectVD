import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.HasPrimitives
import VD.MathlibPending.HarmonicContOnCl
import VD.MathlibPending.Poisson

open Complex InnerProductSpace Metric Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {c : ℂ} {R : ℝ}

lemma xxx (h : ContinuousOn f (closedBall 0 R)) (hR: 0 < R) :
    ContinuousOn (fun z ↦ wedgeIntegral 0 z f ) (closedBall 0 R) := by
  --intro x hx
  unfold wedgeIntegral
  apply ContinuousOn.add
  · simp
    have : (fun (z : ℂ) ↦ ∫ (x : ℝ) in 0..z.re, f ↑x) = (fun a ↦ ∫ (x : ℝ) in 0..a, f x) ∘ (fun z ↦ z.re) := by
      rfl
    rw [this]
    apply ContinuousOn.comp (s := (closedBall 0 R)) (t := Set.uIcc (-R) R)
    · apply intervalIntegral.continuousOn_primitive_interval'
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.comp (t := (closedBall 0 R))
        · exact h
        · fun_prop
        · intro x hx
          simp_all [Set.mem_uIcc]
          grind
      · grind [Set.mem_uIcc]
    · fun_prop
    · intro x hx
      have : -R ≤ R := by
        grind
      simp [Set.uIcc_of_le this, Set.mem_Icc]
      simp_all
      rw [← abs_le]
      trans ‖x‖
      · exact abs_re_le_norm x
      · exact hx
  · intro z hz


    sorry
