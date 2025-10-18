import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Topology.LocallyFinsupp

@[simp]
theorem WithTop.untop₀_max {α : Type*} [AddCommGroup α] [LinearOrder α] {a b : WithTop α}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (max a b).untop₀ = max a.untop₀ b.untop₀ := by
  lift a to α using ha
  lift b to α using hb
  simp only [untop₀_coe]
  by_cases h : a ≤ b
  · simp [max_eq_right h, max_eq_right (coe_le_coe.mpr h)]
  rw [not_le] at h
  simp [max_eq_left h.le, max_eq_left (coe_lt_coe.mpr h).le]

@[simp]
theorem WithTop.untop₀_min {α : Type*} [AddCommGroup α] [LinearOrder α] {a b : WithTop α}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (min a b).untop₀ = min a.untop₀ b.untop₀ := by
  lift a to α using ha
  lift b to α using hb
  simp only [untop₀_coe]
  by_cases h : a ≤ b
  · simp [min_eq_left h, min_eq_left (coe_le_coe.mpr h)]
  rw [not_le] at h
  simp [min_eq_right h.le, min_eq_right (coe_lt_coe.mpr h).le]

@[simp]
theorem WithTop.le_of_untop₀_le_untop₀ {α : Type*} [AddCommGroup α] [LinearOrder α] {a b : WithTop α}
    (ha : a ≠ ⊤) (h : a.untop₀ ≤ b.untop₀) :
    a ≤ b := by
  lift a to α using ha
  by_cases hb : b = ⊤
  · simp_all
  lift b to α using hb
  simp_all

@[simp]
theorem WithTop.untop₀_le_untop₀_of_le {α : Type*} [AddCommGroup α] [LinearOrder α] {a b : WithTop α}
    (hb : b ≠ ⊤) (h : a ≤ b) :
    a.untop₀ ≤ b.untop₀ := by
  lift b to α using hb
  by_cases ha : a = ⊤
  · simp_all
  lift a to α using ha
  simp_all

@[to_additive]
theorem leOnePart_min {Y : Type*} [CommGroup Y] [LinearOrder Y] [MulLeftMono Y] (a b : Y) :
    (min a b)⁻ᵐ = max a⁻ᵐ b⁻ᵐ := by
  rcases lt_trichotomy a b with h | h | h
  · rw [min_eq_left h.le, max_comm, max_eq_right ((le_iff_oneLePart_leOnePart a b).1 h.le).2]
  · simp_all
  · rw [min_comm, min_eq_left h.le, max_eq_right ((le_iff_oneLePart_leOnePart b a).1 h.le).2]

@[to_additive]
theorem leOnePart_max {Y : Type*} [CommGroup Y] [LinearOrder Y] [MulLeftMono Y] (a b : Y) :
    (max a b)⁻ᵐ = min a⁻ᵐ b⁻ᵐ := by
  rcases lt_trichotomy a b with h | h | h
  · rw [max_eq_right h.le, min_comm, min_eq_left ((le_iff_oneLePart_leOnePart a b).1 h.le).2]
  · simp_all
  · rw [min_comm, max_eq_left h.le, min_eq_right ((le_iff_oneLePart_leOnePart b a).1 h.le).2]

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
