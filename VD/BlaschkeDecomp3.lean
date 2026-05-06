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

/-!
## Formula goes here
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {x c w : ℂ}

lemma zz
    {f h : ℂ → E}
    (hw : w ∈ ball 0 R)
    (h₀f : MeromorphicOn f (closedBall 0 R)) -- can be deduced
    (h₁h : AnalyticOnNhd ℂ h (closedBall 0 R))
    (h₂h : ∀ u ∈ (closedBall 0 R), h u ≠ 0)
    (h₁f : f =ᶠ[codiscreteWithin (closedBall 0 R)]
      ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
        * (∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h) :
    h w
      = ((∏ᶠ i, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f (ball 0 R) i))
          * (∏ᶠ i, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f (sphere 0 R)) i))
          • meromorphicTrailingCoeffAt f w := by
  have h₂f : (divisor f (sphere 0 R)).support.Finite :=
    (divisor f (sphere 0 R)).finiteSupport (isCompact_sphere 0 R)
  have h₃f : (divisor f (ball 0 R)).support.Finite := by
    apply ((divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
    intro b hb
    have h₂b := hb
    rw [mem_support, ne_eq, divisor_apply (fun c hc ↦ h₀f c (ball_subset_closedBall hc))
      ((divisor f (ball 0 R)).supportWithinDomain hb)] at h₂b
    rwa [mem_support, ne_eq, divisor_apply h₀f
      (ball_subset_closedBall ((divisor f (ball 0 R)).supportWithinDomain hb))]
  --
  have : meromorphicTrailingCoeffAt f w
      = ((∏ᶠ i, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (-(divisor f (ball 0 R)) i)) *
        ∏ᶠ i, meromorphicTrailingCoeffAt (· - i) w ^ (divisor f (sphere 0 R)) i) • h w := by
    have η₀ : w ∈ closedBall 0 R := ball_subset_closedBall hw
    have := (h₁h w η₀).meromorphicAt
    have η₁ : Preperfect (closedBall (0 : ℂ) R) := by
      rw [← closure_ball _ (pos_of_mem_ball hw).ne']
      exact isOpen_ball.perfect_closure.2
    rw [meromorphicTrailingCoeffAt_congr_nhdsNE ((h₀f w (ball_subset_closedBall
      hw)).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect (by fun_prop) η₀ η₁ h₁f)]
    rw [finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _ (by aesop)]
    rw [finprod_eq_prod_of_mulSupport_subset (s := h₂f.toFinset) _ (by aesop)]
    rw [finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _ (by aesop)]
    rw [finprod_eq_prod_of_mulSupport_subset (s := h₂f.toFinset) _ (by aesop)]
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_smul (by fun_prop)
      (h₁h w (ball_subset_closedBall hw)).meromorphicAt]
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop) (by fun_prop)]
    rw [meromorphicTrailingCoeffAt_prod (by fun_prop)]
    rw [meromorphicTrailingCoeffAt_prod (by fun_prop)]
    rw [(h₁h w (ball_subset_closedBall hw)).meromorphicTrailingCoeffAt_of_ne_zero
      (h₂h w (ball_subset_closedBall hw))]
    congr
    · ext n
      rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)]
    · ext n
      rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)]
  --
  rw [this]
  rw [smul_smul]
  rw [finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _ (by aesop)]
  rw [finprod_eq_prod_of_mulSupport_subset (s := h₂f.toFinset) _ (by aesop)]
  rw [finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _ (by aesop)]
  rw [finprod_eq_prod_of_mulSupport_subset (s := h₂f.toFinset) _ (by aesop)]
  have {a b c d : ℂ} : (a * b) * (c * d) = (a * c) * (b * d) := by
    ring
  rw [← this]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [Finset.prod_eq_one, Finset.prod_eq_one]
  simp
  --
  intro x hx
  rw [← zpow_add₀]
  simp
  rw [meromorphicTrailingCoeffAt_id_sub_const]
  grind
  --
  intro x hx
  rw [← zpow_add₀]
  simp
  apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero
  fun_prop
  apply meromorphicOrderAt_canonicalFactor_ne_top
  exact pos_of_mem_ball hw

lemma zz'
    {f h : ℂ → E}
    (hw : w ∈ ball 0 R)
    (h₁w : meromorphicOrderAt f w = 0)
    (h₀f : MeromorphicOn f (closedBall 0 R)) -- can be deduced
    (h₁h : AnalyticOnNhd ℂ h (closedBall 0 R))
    (h₂h : ∀ u ∈ (closedBall 0 R), h u ≠ 0)
    (h₁f : f =ᶠ[codiscreteWithin (closedBall 0 R)]
      ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
        * (∏ᶠ u, (· - u) ^ (divisor f (sphere 0 R)) u)) • h) :
    h w = ((∏ᶠ i, (canonicalFactor R i w) ^ (divisor f (ball 0 R) i))
          * (∏ᶠ i, (w - i) ^ (-divisor f (sphere 0 R)) i))
          • meromorphicTrailingCoeffAt f w := by
  rw [zz hw h₀f h₁h h₂h h₁f]
  congr
  · ext x
    by_cases h : x = w
    · subst h
      rw [divisor_apply]
      simp_all
      intro z hz
      apply h₀f z
      apply ball_subset_closedBall hz
      exact hw
    by_cases h₁ : (divisor f (ball 0 R)) x = 0
    · simp_all
    rw [AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero]
    apply Complex.analyticOnNhd_canonicalFactor
    aesop
    apply Complex.canonicalFactor_ne_zero

    have : x ∈ (divisor f (ball 0 R)).support := by aesop
    exact (divisor f (ball 0 R)).supportWithinDomain this
    --
    exact ball_subset_closedBall hw
    tauto
  · ext x
    by_cases h : x = w
    · subst h
      rw [meromorphicTrailingCoeffAt_id_sub_const]
      simp
      rw [zero_zpow_eq]
      simp
      rw [divisor_def]
      aesop
    rw [meromorphicTrailingCoeffAt_id_sub_const]
    aesop
