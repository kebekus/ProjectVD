import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import VD.MathlibSubmitted.DivisorOrder

open Function MeromorphicOn Metric Real Set Classical ValueDistribution

namespace locallyFinsuppWithin

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*}

lemma restrictPosPart {V : Set X} (D : locallyFinsuppWithin U ℤ) (h : V ⊆ U) :
    D⁺.restrict h = (D.restrict h)⁺ := by
  ext x
  simp [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.posPart_apply]
  aesop

end locallyFinsuppWithin


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

  have {r : ℝ} : (locallyFinsuppWithin.toClosedBall r) (divisor (fun z ↦ f z - a) univ)⁺
      = (divisor (fun z ↦ f z - a) (closedBall 0 |r|))⁺ := by
    unfold locallyFinsuppWithin.toClosedBall
    simp
    rw [locallyFinsuppWithin.restrictPosPart]
    rw [MeromorphicOn.divisor_restrict]
    apply h.sub
    exact MeromorphicOn.const a
  simp_rw [this]


  sorry
