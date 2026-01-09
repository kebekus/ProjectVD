import VD.MathlibSubmitted.Nevanlinna_add_characteristic
--import Mathlib.MeasureTheory.Integral.Prod
import Mathlib

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution

/-
Establish parity and monotonocity of the Nevanlinna functions.
-/


namespace Function.locallyFinsuppWithin

variable
  {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/--
The logarithmic counting function is even.
-/
lemma logCounting_even (D : locallyFinsuppWithin (univ : Set E) ℤ) :
    (logCounting D).Even := fun r ↦ by simp [logCounting, toClosedBall, restrict_apply]

end Function.locallyFinsuppWithin

namespace ValueDistribution

/--
The logarithmic counting function is even.
-/
theorem logCounting_even {f : ℂ → ℂ} {a : WithTop ℂ} :
    Function.Even (logCounting f a) := by
  intro r
  by_cases h : a = ⊤
  all_goals
  · simp [logCounting, h, Function.locallyFinsuppWithin.logCounting_even _ r]

/--
The proximity function is even.
-/
theorem proximity_even {f : ℂ → ℂ} {a : WithTop ℂ} :
    Function.Even (proximity f a) := by
  intro r
  by_cases h : a = ⊤
  all_goals
  · simp [proximity, h]

/--
The characteristic function is even.
-/
theorem characteristic_even {f : ℂ → ℂ} {a : WithTop ℂ} :
    Function.Even (characteristic f a) :=
  Function.Even.add proximity_even logCounting_even

theorem logCounting_monotoneOn {f : ℂ → ℂ} {a : WithTop ℂ} (h : Meromorphic f) :
    MonotoneOn (logCounting f a) Set.univ := by
  intro a ha b hb hab
  unfold logCounting
  sorry

theorem characteristic_monotoneOn {f : ℂ → ℂ} {a : WithTop ℂ} (h : Meromorphic f) :
    MonotoneOn (characteristic f a) Set.univ := by
  intro a ha b hb hab
  sorry

end ValueDistribution
