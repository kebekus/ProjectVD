import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.JensenFormula
import VD.MathlibSubmitted.BlaschkeDecomp

open Complex Filter Function MeromorphicOn Metric Real Set Classical Topology --ValueDistribution

/-!
## Additional Material
-/


theorem MeromorphicOn.codiscreteWithin_setOf_meromorphicOrderAt_eq_zero_or_top {U : Set ℂ} {f : ℂ → ℂ}
    (h₁f : MeromorphicOn f U)
    (h₂f : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤) :
    {u ∈ U | meromorphicOrderAt f u = 0 ∨ meromorphicOrderAt f u = ⊤} ∈ codiscreteWithin U := by
  convert mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
    h₁f.codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top
  aesop

theorem MeromorphicOn.codiscreteWithin_setOf_ne_zero {U : Set ℂ} {f : ℂ → ℂ}
    (h₁f : MeromorphicOn f U)
    (h₂f : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤) :
    ∀ᶠ x in codiscreteWithin U, f x ≠ 0 := by
  filter_upwards [h₁f.analyticAt_mem_codiscreteWithin,
    h₁f.codiscreteWithin_setOf_meromorphicOrderAt_eq_zero_or_top h₂f] with x h₁x h₂x
  have := h₂f x h₂x.1
  simp_all [← h₁x.analyticOrderAt_eq_zero, h₁x.meromorphicOrderAt_eq]

theorem finprod_ne_zero {ι : Type*} {M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
  {f : ι → M₀} (h : ∀ i, f i ≠ 0) :
    ∏ᶠ i, f i ≠ 0 := by
  by_cases h₂ : Set.Finite f.mulSupport
  · grind [finprod_eq_prod f h₂, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]
