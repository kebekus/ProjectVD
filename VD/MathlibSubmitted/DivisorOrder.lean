import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Topology.LocallyFinsupp

namespace Function.locallyFinsuppWithin

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*} [AddCommGroup Y] [LinearOrder Y]

lemma posPart_apply (a : locallyFinsuppWithin U Y) (x : X) :
    a⁺ x = (a x)⁺ := rfl

lemma negPart_apply (a : locallyFinsuppWithin U Y) (x : X) :
    a⁻ x = (a x)⁻ := rfl

variable [IsOrderedAddMonoid Y]

/--
The negative part of a minimum is the maximum of the negative parts.
-/
theorem negPart_min (a b : locallyFinsuppWithin U Y) :
    (min a b)⁻ = max a⁻ b⁻ := by
  ext x
  apply _root_.negPart_min

/--
The negative part of a maximum is the minimum of the negative parts.
-/
theorem negPart_max (a b : locallyFinsuppWithin U Y) :
    (max a b)⁻ = min a⁻ b⁻ := by
  ext x
  apply _root_.negPart_max

/--
Taking the positive part of a function with locally finite support commutes with
scalar multiplication by a natural number.
-/
theorem nsmul_posPart
    {X : Type*} [TopologicalSpace X] {U : Set X}
    {Y : Type*} [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]
    (f : Function.locallyFinsuppWithin U Y) (n : ℕ) :
    n • f⁺ = (n • f)⁺ := by
  unfold instPosPart
  ext x
  simp only [Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  by_cases h : f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

/--
Taking the negative part of a function with locally finite support commutes with
scalar multiplication by a natural number.
-/
theorem nsmul_negPart
    {X : Type*} [TopologicalSpace X] {U : Set X}
    {Y : Type*} [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]
    (f : Function.locallyFinsuppWithin U Y) (n : ℕ) :
    n • f⁻ = (n • f)⁻ := by
  unfold instNegPart
  ext x
  simp only [Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply,
    Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  by_cases h : -f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

end Function.locallyFinsuppWithin
