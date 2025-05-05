import Mathlib.Analysis.Meromorphic.FactorizedRational
import VD.ToMathlib.LeadCoefficient

open Function.FactorizedRational MeromorphicAt MeromorphicOn

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Theorems about the leading coefficient
-/

theorem meromorphicAt_prod  {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    MeromorphicAt (∏ n ∈ s, f n) x := by
  classical
  apply Finset.induction (motive := fun s ↦ MeromorphicAt (∏ n ∈ s , f n) x)
  · rw [Finset.prod_empty]
    exact analyticAt_const.meromorphicAt
  · intro σ s hσ hind
    rw [Finset.prod_insert hσ]
    exact (h σ).mul hind

theorem leadCoefficient_const {x : 𝕜} {e : 𝕜} :
    leadCoefficient (fun _ ↦ e) x = e := by
  by_cases he : e = 0
  · rw [he]
    apply analyticAt_const.meromorphicAt.leadCoefficient_of_order_eq_top
    rw [MeromorphicAt.order_eq_top_iff]
    simp
  · exact analyticAt_const.leadCoefficient_of_nonvanish he

theorem leadCoefficient_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    leadCoefficient (∏ n ∈ s, f n) x = ∏ n ∈ s, leadCoefficient (f n) x := by
  classical
  apply Finset.induction
    (motive := fun b' ↦ (leadCoefficient (∏ n ∈ b' , f n) x = ∏ n ∈ b', leadCoefficient (f n) x))
  · simp only [Finset.univ_eq_empty, Finset.prod_empty, forall_const]
    apply leadCoefficient_const
  · intro σ s₁ hσ hind
    rw [Finset.prod_insert hσ, Finset.prod_insert hσ, leadCoefficient_mul (h σ) (meromorphicAt_prod h),
      hind]

theorem Function.FactorizedRational.leadCoefficient {d : 𝕜 → ℤ} {x : 𝕜}
    (h₁ : d.support.Finite) (h₂ : x ∉ d.support) :
    leadCoefficient (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ d u := by
  have : (fun u ↦ (· - u) ^ d u).mulSupport ⊆ h₁.toFinset := by
    sorry
  rw [finprod_eq_prod_of_mulSupport_subset _ this]
  rw [leadCoefficient_prod]
  have : (fun u ↦ (x - u) ^ d u).mulSupport ⊆ h₁.toFinset := by
    sorry
  rw [finprod_eq_prod_of_mulSupport_subset _ this]
  apply Finset.prod_congr rfl
  intro y hy
  rw [leadCoefficient_zpow₁ (by fun_prop)]
  congr
  rw [AnalyticAt.leadCoefficient_of_nonvanish (by fun_prop)]
  --
  · by_contra hCon
    simp_all [sub_eq_zero]
  --

  rw [MeromorphicAt.order_ne_top_iff]
  sorry
  exact fun _ ↦ by fun_prop
