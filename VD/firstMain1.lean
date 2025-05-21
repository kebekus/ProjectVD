import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.CircleIntegral
import VD.ToMathlib.meromorphicOn_integrability
import VD.stronglyMeromorphic_JensenFormula
import VD.ProximityFunction
import VD.ToMathlib.CharacteristicFunction
import Mathlib.Analysis.Complex.ValueDistribution.CountingFunction

open Asymptotics Real


-- Lang p. 164

theorem MeromorphicOn.restrict
  {f : ℂ → ℂ}
  (h₁f : MeromorphicOn f ⊤)
  (r : ℝ) :
  MeromorphicOn f (Metric.closedBall 0 r) := by
  exact fun x a => h₁f x trivial

theorem MeromorphicOn.restrict_inv
  {f : ℂ → ℂ}
  (h₁f : MeromorphicOn f ⊤)
  (r : ℝ) :
  h₁f.inv.restrict r = (h₁f.restrict r).inv := by
  funext x
  simp

--

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  --{f g : ℂ → E} {a : WithTop E} {a₀ : E}


theorem Nevanlinna_firstMain₁
  {f : ℂ → ℂ}
  (h₁f : MeromorphicOn f ⊤)
  (h₂f : MeromorphicNFAt f 0)
  (h₃f : f 0 ≠ 0) :
  (fun _ ↦ log ‖f 0‖) = ValueDistribution.characteristic f ⊤ - ValueDistribution.characteristic f⁻¹ ⊤ := by

  classical

  unfold ValueDistribution.characteristic

  have {A B C D : ℝ → ℝ} : A + B - (C + D) = A - C - (D - B) := by
    ring
  rw [this]
  clear this

  rw [ValueDistribution.logCounting_inv]
  rw [← ValueDistribution.log_counting_zero_sub_logCounting_top]
  unfold Function.locallyFinsuppWithin.logCounting
  have XX {r : ℝ} : (MeromorphicOn.divisor f ⊤).toClosedBall r  = MeromorphicOn.divisor f (Metric.closedBall 0 |r|) := by
    unfold Function.locallyFinsuppWithin.toClosedBall
    exact MeromorphicOn.divisor_restrict h₁f fun ⦃a⦄ a ↦ trivial
  simp_all
  clear XX
  have ZZ : (MeromorphicOn.divisor f Set.univ) 0 = 0 := by
    rw [MeromorphicOn.divisor_apply]
    simp_rw [← h₂f.order_eq_zero_iff] at h₃f
    simp_rw [h₃f]
    exact rfl
    assumption
    trivial
  rw [ValueDistribution.proximity_sub_proximity_inv_eq_circleAverage]
  --rw [ZZ]
  --simp
  funext r
  simp
  --rw [← Nevanlinna_proximity h₁f]

  by_cases h₁r : r = 0
  · rw [h₁r]
    simp

  by_cases hr : 0 < r
  · let A := jensen hr f (h₁f.restrict r) h₂f h₃f
    --simp at A
    rw [A]
    simp_rw [← h₂f.order_eq_zero_iff] at h₃f
    rw [h₃f]
    clear A
    simp
    have {A B : ℝ} : -A + B = B - A := by ring
    rw [this]
    have : |r| = r := by
      rw [← abs_of_pos hr]
      simp
    rw [this]
    congr
    simp

  -- case 0 < -r
  have h₂r : 0 < -r := by
    simp [h₁r, hr]

    by_contra hCon
    -- Assume ¬(r < 0), which means r >= 0
    push_neg at hCon
    -- Now h is r ≥ 0, so we split into cases
    rcases lt_or_eq_of_le hCon with h|h
    · tauto
    · tauto
  let A := jensen h₂r f (h₁f.restrict (-r)) h₂f h₃f
  simp at A
  rw [A]
  clear A
  --simp
  have {A B : ℝ} : -A + B = B - A := by ring
  rw [this]

  congr 1
  congr 1
  simp
  let A := integrabl_congr_negRadius (f := (fun z ↦ log (norm (f z)))) (r := r) (c := 0)
  rw [A]
  have : |r| = -r := by
    rw [← abs_of_pos h₂r]
    simp
  rw [this]
  simp_rw [← h₂f.order_eq_zero_iff] at h₃f
  rw [h₃f]
  simp
  assumption
