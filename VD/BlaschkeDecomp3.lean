import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.JensenFormula
import VD.MathlibSubmitted.BlaschkeDecomp

open Complex Filter Function MeromorphicOn Metric Real Set Classical Topology --ValueDistribution

/-!
## Additional Material
-/

@[fun_prop]
lemma meromorphicAt_canonicalFactor {R : ℝ} {x w : ℂ} : MeromorphicAt (canonicalFactor R w) x := by
  rw [canonicalFactor_def]
  fun_prop

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {U : Set 𝕜}

/-!
## Formula goes here
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {x c w : ℂ} {f h : ℂ → E}

/--
Companion lemma to
`congr_codiscreteWitin_closedBall_prod_canonicalFactor_mul_prod_smul`: In the
setting of the extended canonical decomposition, write the function `h` entirely
in terms of `f`.
-/
lemma AnalyticOnNhd.eq_smul_meromorphicTrailingCoeffAt_of_eventuallyEq
    (h₁h : AnalyticOnNhd ℂ h (closedBall 0 R)) (h₂h : ∀ u ∈ (closedBall 0 R), h u ≠ 0)
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : f =ᶠ[codiscreteWithin (closedBall 0 R)]
      ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
        * (∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h)
    (hw : w ∈ closedBall 0 R) (hR : 0 < R) :
    h w
      = ((∏ᶠ i, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f (ball 0 R) i))
          * (∏ᶠ i, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f (sphere 0 R)) i))
          • meromorphicTrailingCoeffAt f w := by
  -- Finiteness properties and side results used throughout the proof
  have h₃f : (divisor f (sphere 0 R)).support.Finite :=
    (divisor f (sphere 0 R)).finiteSupport (isCompact_sphere 0 R)
  have h₄f : (divisor f (ball 0 R)).support.Finite := by
    apply ((divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
    intro b hb
    rw [mem_support, ne_eq, divisor_apply h₁f
      (ball_subset_closedBall ((divisor f (ball 0 R)).supportWithinDomain hb))]
    rwa [mem_support, ne_eq, divisor_apply (fun c hc ↦ h₁f c (ball_subset_closedBall hc))
      ((divisor f (ball 0 R)).supportWithinDomain hb)] at hb
  have := (h₁h w hw).meromorphicAt
  -- Proof body: Substitute `f` using `h₁f` and compute
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
    ((h₁f w hw).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (by fun_prop) hw _ h₂f),
    finprod_eq_prod_of_mulSupport_subset (s := h₄f.toFinset) _ (by aesop),
    finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _ (by aesop),
    finprod_eq_prod_of_mulSupport_subset (s := h₄f.toFinset) _ (by aesop),
    finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _ (by aesop),
    MeromorphicAt.meromorphicTrailingCoeffAt_smul (by fun_prop) (h₁h w hw).meromorphicAt,
    MeromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop) (by fun_prop),
    meromorphicTrailingCoeffAt_prod (by fun_prop), meromorphicTrailingCoeffAt_prod (by fun_prop),
    (h₁h w hw).meromorphicTrailingCoeffAt_of_ne_zero (h₂h w hw), smul_smul, mul_mul_mul_comm,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Finset.prod_eq_one, Finset.prod_eq_one,
    mul_one, one_smul]
  · intro x hx
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop), ← zpow_add₀,
      locallyFinsuppWithin.coe_neg, Pi.neg_apply, neg_add_cancel, zpow_zero]
    rw [meromorphicTrailingCoeffAt_id_sub_const]
    grind
  · intro x hx
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop), ← zpow_add₀, add_neg_cancel,
      zpow_zero]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (by fun_prop)
      (meromorphicOrderAt_canonicalFactor_ne_top x hR)
  · rw [← closure_ball _ hR.ne']
    exact isOpen_ball.perfect_closure.2

/--
Companion lemma to
`congr_codiscreteWitin_closedBall_prod_canonicalFactor_mul_prod_smul`: In the
setting of the extended canonical decomposition, write the function `h` entirely
in terms of `f`.
-/
lemma AnalyticOnNhd.eq_smul_meromorphicTrailingCoeffAt_of_eventuallyEq_of_meromorphicOrderAt
    (h₁h : AnalyticOnNhd ℂ h (closedBall 0 R)) (h₂h : ∀ u ∈ (closedBall 0 R), h u ≠ 0)
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : f =ᶠ[codiscreteWithin (closedBall 0 R)]
      ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
        * (∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h)
    (h₁w : w ∈ closedBall 0 R)
    (h₂w : meromorphicOrderAt f w = 0)
    (hR : 0 < R) :
    h w = ((∏ᶠ i, (canonicalFactor R i w) ^ (divisor f (ball 0 R) i))
          * (∏ᶠ i, (w - i) ^ (-divisor f (sphere 0 R)) i))
          • meromorphicTrailingCoeffAt f w := by
  rw [h₁h.eq_smul_meromorphicTrailingCoeffAt_of_eventuallyEq h₂h h₁f h₂f h₁w hR]
  congr
  · ext x
    by_cases h₁x : x ∉ ball 0 R
    · simp_all
    by_cases h₂x : x = w
    · subst h₂x
      simp_all [(h₁f.mono_set ball_subset_closedBall).divisor_apply (not_notMem.mp h₁x)]
    by_cases h₃x : (divisor f (ball 0 R)) x = 0
    · simp_all
    rw [AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero
      (Complex.analyticOnNhd_canonicalFactor R x w (by aesop))
      (Complex.canonicalFactor_ne_zero (by aesop) h₁w (by tauto))]
  · ext x
    by_cases h : x = w
    · simp_all [meromorphicTrailingCoeffAt_id_sub_const, divisor_def]
    grind [meromorphicTrailingCoeffAt_id_sub_const]
