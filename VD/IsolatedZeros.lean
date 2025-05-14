import Mathlib.Analysis.Meromorphic.Basic

open Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {x : 𝕜} {f g : 𝕜 → E}

/-!
## Theorems concerning MeromorphicAt
-/

theorem MeromorphicAt.frequently_zero_iff_eventually_zero
    (hf : MeromorphicAt f x) :
    (∃ᶠ z in 𝓝[≠] x, f z = 0) ↔ ∀ᶠ z in 𝓝[≠] x, f z = 0 :=
  ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right,
    fun h ↦ h.frequently⟩

theorem MeromorphicAt.frequently_zero_iff_eventuallyEq_zero
    (hf : MeromorphicAt f x) :
    (∃ᶠ z in 𝓝[≠] x, f z = 0) ↔ f =ᶠ[𝓝[≠] x] 0 :=
  ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right,
    fun h ↦ h.frequently⟩

/--
Variant of the principle of isolated zeros: Let `U` be a subset of `𝕜` and
assume that `x ∈ U` is not an isolated point of `U`. If a function `f` is
meromorphic at `x` and vanishes along a subset that is codiscrete within `U`,
then `f` vanishes in a punctured neighbourhood of `f`.

For a typical application, let `U` be a closed ball and let `x` be a point on
the circumference. If `f` is meromorphic at `x` and vanishes on `U`, then it
will vanish in a punctured neighbourhood of `x`, which intersects `U`
non-trivally but is not contained in `U`.

The assumption that `x` is not an isolated point of `U` is expressed in `h₂x` as
`Uᶜ ∉ 𝓝[≠] x`.
-/
theorem MeromorphicAt.eventuallyEq_zero_nhdNE_of_eventuallyEq_zero_codiscreteWithin
    (hf : MeromorphicAt f x)
    (h₁x : x ∈ U)
    (h₂x : Uᶜ ∉ 𝓝[≠] x)
    (h : f =ᶠ[Filter.codiscreteWithin U] 0) :
    f =ᶠ[𝓝[≠] x] 0 := by
  rw [← (hf).frequently_zero_iff_eventuallyEq_zero]
  by_contra hCon
  rw [Filter.EventuallyEq, Filter.Eventually, mem_codiscreteWithin] at h
  have := h x h₁x
  simp only [Pi.zero_apply, Filter.disjoint_principal_right, Set.compl_diff] at this
  have := Filter.inter_mem (Filter.not_frequently.1 hCon) this
  simp_all [Set.inter_union_distrib_left, (by tauto_set : {x | ¬f x = 0} ∩ {x | f x = 0} = ∅)]

/--
Variant of the principle of isolated zeros: Let `U` be a subset of `𝕜` and
assume that `x ∈ U` is not an isolated point of `U`. If a function `f` is
meromorphic at `x` and vanishes along a subset that is codiscrete within `U`,
then `f` vanishes in a punctured neighbourhood of `f`.

For a typical application, let `U` be the closure of the Mandelbrot set and let
`x` be a point in its frontier. If `f` is meromorphic at `x` and vanishes on
`U`, then it will vanish in a punctured neighbourhood of `x`, even though this
neighbourhood is not contained in `U`.
-/
theorem MeromorphicAt.eventuallyEq_nhdNE_of_eventuallyEq_codiscreteWithin
    (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x)
    (h₁x : x ∈ U)
    (h₂x : Uᶜ ∉ 𝓝[≠] x)
    (h : f =ᶠ[Filter.codiscreteWithin U] g) :
    f =ᶠ[𝓝[≠] x] g := by
  rw [Filter.eventuallyEq_iff_sub] at *
  apply (hf.sub hg).eventuallyEq_zero_nhdNE_of_eventuallyEq_zero_codiscreteWithin h₁x h₂x h
