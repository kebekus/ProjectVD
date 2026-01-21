import Mathlib.Topology.LocallyFinsupp

open Filter Function Set

/-!
# Asymptotic Behaviour of Logarithmic Counting Functions


Prove that the logarithmic counting function of a meromorphic function `f` is
bounded if and only if `f` is analytic.
-/

namespace Function.locallyFinsuppWithin

variable
  {X : Type*} [TopologicalSpace X]

/-!
## Singleton Indicators as Functions with Locally Finite Support
-/

/--
Is analogy to `Finsupp.single`, this definition presents the indicator function
of a single point as a function with locally finite support.
-/
noncomputable def single (x : X) : locallyFinsuppWithin (Set.univ : Set X) ℤ where
  toFun := by
    classical
    exact (if · = x then 1 else 0)
  supportWithinDomain' z hz := by tauto
  supportLocallyFiniteWithinDomain' := by
    intro _ _
    use ⊤
    simp only [top_eq_univ, univ_mem, univ_inter, true_and]
    convert (finite_singleton x)
    aesop

open Classical in
/--
Simplifier lemma: `single e` takes the value `1` at `e` and is zero otherwise.
-/
@[simp] lemma single_eval {x₁ x₂ : X} :
    single x₁ x₂ = if x₂ = x₁ then 1 else 0 := rfl

/--
The function `single e` is positive.
-/
@[simp] lemma single_pos {x : X} : 0 < single x := by
  apply lt_of_le_of_ne
  · intro y
    by_cases he : y = x
    all_goals
      simp_all [single_eval]
  · apply DFunLike.ne_iff.2
    use x
    simp [single_eval]

/--
Every positive function with locally finite supports dominates a singleton
indicator.
-/
lemma exists_single_le_pos {D : locallyFinsuppWithin (Set.univ : Set X) ℤ} (h : 0 < D) :
    ∃ e, single e ≤ D := by
  obtain ⟨z, hz⟩ := (by simpa [D.ext_iff] using (ne_of_lt h).symm : ∃ z, D z ≠ 0)
  use z
  intro e
  by_cases he : e = z
  · subst he
    simpa [single_eval] using Int.lt_iff_le_and_ne.mpr ⟨h.le e, hz.symm⟩
  · simpa [he, single_eval] using h.le e

end Function.locallyFinsuppWithin
