import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Int.Cast.Pi
import Mathlib.Topology.LocallyFinsupp

open Filter Set

variable
  {X : Type*} [TopologicalSpace X]

@[simp]
lemma Function.locallyFinsuppWithin.coe_sum [DecidableEq X] {ι : Type*} [DecidableEq ι] {U : Set X} {s : Finset ι} {F : ι → Function.locallyFinsuppWithin U ℤ} :
    (↑(∑ n ∈ s, F n) : X → ℤ) = ∑ n ∈ s, (F n : X → ℤ) := by
  induction s using Finset.induction with
  | empty => simp_all
  | insert => simp_all

@[simp]
lemma Function.locallyFinsuppWithin.coe_finsum [DecidableEq X] {U : Set X} {ι : Type*} [DecidableEq ι]
    {F : ι → Function.locallyFinsuppWithin U ℤ} :
    (↑(∑ᶠ i, F i) : X → ℤ) = ∑ᶠ i, (F i : X → ℤ) := by
  have : F.support = (fun i ↦ (F i : X → ℤ)).support := by
    ext i
    contrapose
    exact ⟨by simp_all, by simpa using (F i).coe_injective (a₂ := 0)⟩
  by_cases h : F.support.Finite
  · rw [finsum_eq_sum F h, Function.locallyFinsuppWithin.coe_sum]
    have h₂ : (fun i ↦ (F i : X → ℤ)).support.Finite := by simp_all
    simp_all [finsum_eq_sum _ h₂]
  · simp_all [finsum_of_infinite_support]

/--
Present a function with with finite support as a linear combination of singleton indicator functions.
-/
@[simp]
lemma Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self [DecidableEq X] {U : Set X}
    {F : Function.locallyFinsuppWithin U ℤ} (h : F.support.Finite) :
    ∑ x ∈ h.toFinset, (F x) • ((single x (1 : ℤ)).restrict (subset_univ U)) = F := by
  ext z
  by_cases hz : z ∉ U
  · aesop
  simp only [coe_sum, coe_zsmul, zsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply,
    Int.cast_eq, restrict_apply]
  by_cases hz : z ∈ F.support
  · rw [← Finset.add_sum_erase _ _ (by aesop : z ∈ h.toFinset), Finset.sum_eq_zero (by aesop)]
    aesop
  · aesop
