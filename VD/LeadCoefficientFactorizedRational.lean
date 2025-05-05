import Mathlib.Analysis.Meromorphic.FactorizedRational
import VD.ToMathlib.LeadCoefficient

open Function.FactorizedRational MeromorphicAt MeromorphicOn

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Theorems about the leading coefficient
-/

theorem leadCoefficient_const {x : 𝕜} {e : 𝕜} :
    leadCoefficient (fun _ ↦ e) x = e := by
  by_cases he : e = 0
  · rw [he]
    apply analyticAt_const.meromorphicAt.leadCoefficient_of_order_eq_top
    rw [MeromorphicAt.order_eq_top_iff]
    simp
  · exact analyticAt_const.leadCoefficient_of_nonvanish he

theorem leadCoefficient_prod {ι : Type*} {s : Finset ι} {f : s → 𝕜 → 𝕜} {x : 𝕜} :
    leadCoefficient (∏ n, f n) x = ∏ n, leadCoefficient (f n) x := by
  classical
  apply Finset.induction (motive := fun s' ↦
    (∀ f' : s' → 𝕜 → 𝕜, leadCoefficient (∏ n, f' n) x = ∏ n, leadCoefficient (f' n) x))
  · simp only [Finset.univ_eq_empty, Finset.prod_empty, forall_const]
    apply leadCoefficient_const
  · intro s a ha hinduction f'
    -- see stronglyMeromorphicOn_eliminate
    sorry


/--
Factorized rational functions are analytic wherever the exponent is non-negative.
-/
theorem Function.FactorizedRational.leadCoefficient {d : 𝕜 → ℤ} {x : 𝕜}
    (h : d.support.Finite) :
    leadCoefficient (∏ᶠ u, (· - u) ^ d u) x = 0 := by

  sorry
