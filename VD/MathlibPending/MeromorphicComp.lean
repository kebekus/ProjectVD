import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Basic

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [gg : IsScalarTower 𝕜 𝕜' E]
  {x : 𝕜} {f : 𝕜' → E}

lemma MeromorphicAt.comp_analyticAt' {g : 𝕜 → 𝕜'}
    (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) : MeromorphicAt (f ∘ g) x := by
  obtain ⟨r, hr⟩ := hf
  by_cases hg' : analyticOrderAt (g · - g x) x = ⊤
  · -- trivial case: `g` is locally constant near `x`
    refine .congr (.const (f (g x)) x) ?_
    filter_upwards [nhdsWithin_le_nhds <| analyticOrderAt_eq_top.mp hg'] with z hz
    grind
  · -- interesting case: `g z - g x` looks like `(z - x) ^ n` times a non-vanishing function
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hg'
    obtain ⟨h, han, hne, heq⟩ := (hg.fun_sub analyticAt_const).analyticOrderAt_eq_natCast.mp hn.symm
    set j := fun z ↦ (z - g x) ^ r • f z
    have := ((han.fun_inv hne).fun_pow r).fun_smul (hr.restrictScalars.comp' hg)
    refine ⟨n * r, this.congr ?_⟩
    filter_upwards [heq, han.continuousAt.tendsto.eventually_ne hne] with z hz hzne
    simp only [j, inv_pow, Function.comp_apply, inv_smul_eq_iff₀ (pow_ne_zero r hzne)]
    rw [hz, smul_comm, ← smul_assoc, pow_mul, smul_pow]

lemma MeromorphicOn.comp_analyticOn {g : 𝕜 → 𝕜'} {s : Set 𝕜} {t : Set 𝕜'}
    (hf : MeromorphicOn f t) (hg : AnalyticOnNhd 𝕜 g s) (hst : Set.MapsTo g s t) : MeromorphicOn (f ∘ g) s :=
  fun x hx ↦ (hf (g x) (hst hx)).comp_analyticAt' (hg x hx)
