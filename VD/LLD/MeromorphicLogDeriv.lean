/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Meromorphic API for the Logarithmic Derivative — LLD work package A

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §3.

Mathlib target: new file `Mathlib/Analysis/Meromorphic/LogDeriv.lean`.
Dependencies: none (independently PR-able).

For a function `f`, Mathlib defines the logarithmic derivative as `logDeriv f = deriv f / f`. This
file establishes meromorphy of `logDeriv f` for meromorphic `f`, computes the relevant meromorphic
orders, and provides congruence and arithmetic lemmas with respect to the codiscrete filter.

- `MeromorphicAt.logDeriv`: pointwise meromorphy of the logarithmic derivative.

- `meromorphicOrderAt_logDeriv_eq_neg_one`: the crucial structural fact that logarithmic
  derivatives have at worst **simple** poles: at zeros and poles of `f`, the meromorphic order of
  `logDeriv f` equals `-1`.

- `meromorphicOrderAt_logDeriv_nonneg`: at points of order zero, the order of `logDeriv f` is
  nonnegative.

- `logDeriv_congr_codiscreteWithin`: on an open set `U`, the logarithmic derivative depends only
  on the equivalence class of the function modulo equality on codiscrete subsets of `U`.

- `MeromorphicOn.logDeriv_mul_eventuallyEq`, `logDeriv_prod_eventuallyEq`,
  `logDeriv_finprod_eventuallyEq`, `MeromorphicOn.logDeriv_zpow_eventuallyEq`,
  `logDeriv_finprod_zpow_eventuallyEq`: away from a codiscrete subset of `U`, the logarithmic
  derivative converts products of meromorphic functions into sums. These are the workhorse lemmas
  for the differentiated Poisson–Jensen formula.

Out of scope here (kept for the Second Main Theorem): `divisor (logDeriv f)` computations and
`N(r, f′/f)`-type bounds.
-/

open Filter Function Set Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f g : 𝕜 → 𝕜'} {x : 𝕜} {U : Set 𝕜}

/-!
## Meromorphy
-/

/-- If `f` is meromorphic at a point, then so is its logarithmic derivative. -/
protected theorem MeromorphicAt.logDeriv [CompleteSpace 𝕜'] (hf : MeromorphicAt f x) :
    MeromorphicAt (logDeriv f) x :=
  hf.deriv.div hf

/-!
## Meromorphic Orders

The logarithmic derivative of a meromorphic function has at worst simple poles, located at the
zeros and poles of the function.
-/

section order

variable [CompleteSpace 𝕜] {f : 𝕜 → 𝕜}

/-- At zeros and poles of a meromorphic function `f`, the logarithmic derivative has a simple
pole: its meromorphic order equals `-1`. -/
theorem meromorphicOrderAt_logDeriv_eq_neg_one [CharZero 𝕜] (hf : MeromorphicAt f x)
    (h₁ : meromorphicOrderAt f x ≠ 0) (h₂ : meromorphicOrderAt f x ≠ ⊤) :
    meromorphicOrderAt (logDeriv f) x = -1 := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, meromorphicOrderAt f x = (n : WithTop ℤ) :=
    Option.ne_none_iff_exists'.mp h₂
  have h₃ : n ≠ 0 := by
    rintro rfl
    exact h₁ (by exact_mod_cast hn)
  rw [show logDeriv f = deriv f / f from rfl, meromorphicOrderAt_div hf.deriv hf,
    meromorphicOrderAt_deriv_eq_sub_one (Int.cast_ne_zero.mpr h₃) hn, hn]
  norm_cast
  rw [show n - 1 - n = -1 by ring]
  rfl

/-- At points where a meromorphic function has order zero, the meromorphic order of the
logarithmic derivative is nonnegative. -/
theorem meromorphicOrderAt_logDeriv_nonneg (hf : MeromorphicAt f x)
    (h : meromorphicOrderAt f x = 0) :
    0 ≤ meromorphicOrderAt (logDeriv f) x := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ :=
    (meromorphicOrderAt_eq_int_iff (n := 0) hf).1 (by exact_mod_cast h)
  have h₄ : f =ᶠ[𝓝[≠] x] g := by
    filter_upwards [h₃g] with z hz
    simpa using hz
  have h₅ : logDeriv f =ᶠ[𝓝[≠] x] logDeriv g := by
    filter_upwards [h₄, h₄.nhdsNE_deriv] with z h₁z h₂z
    rw [logDeriv_apply, logDeriv_apply, h₁z, h₂z]
  rw [meromorphicOrderAt_congr h₅]
  exact (h₁g.deriv.div h₁g h₂g).meromorphicOrderAt_nonneg

end order

/-!
## Congruence

On an open set `U`, the logarithmic derivative only depends on the equivalence class of the
function with respect to equality away from codiscrete subsets of `U`. Note that this statement
is pure calculus and requires no meromorphy assumption.
-/

/-- If two functions agree on a codiscrete subset of an open set `U`, then so do their
logarithmic derivatives. -/
theorem logDeriv_congr_codiscreteWithin (hU : IsOpen U) (h : f =ᶠ[codiscreteWithin U] g) :
    logDeriv f =ᶠ[codiscreteWithin U] logDeriv g := by
  have h' : ∀ y ∈ U, {z | f z = g z} ∪ Uᶜ ∈ 𝓝[≠] y :=
    mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h
  filter_upwards [h, self_mem_codiscreteWithin U] with y h₁y h₂y
  have h₃y : f =ᶠ[𝓝 y] g := by
    have h₄ : {z | f z = g z} ∪ Uᶜ ∈ 𝓝 y := by
      rw [← nhdsNE_sup_pure y, mem_sup]
      exact ⟨h' y h₂y, mem_pure.2 (mem_union_left _ h₁y)⟩
    filter_upwards [h₄, hU.mem_nhds h₂y] with z h₁z h₂z
    rcases h₁z with h₁z | h₁z
    · exact h₁z
    · exact absurd h₂z h₁z
  rw [logDeriv_apply, logDeriv_apply, h₃y.deriv_eq, h₃y.eq_of_nhds]

/-!
## Arithmetic on Codiscrete Sets

The pointwise lemma `logDeriv_mul` requires differentiability and nonvanishing of the factors at
the point in question. For meromorphic functions whose order is nowhere `⊤`, both conditions hold
away from a codiscrete set, turning the pointwise arithmetic into arithmetic of codiscrete
equivalence classes.
-/

/-- A function meromorphic on `U`, with meromorphic order nowhere `⊤`, is nonvanishing away from
a codiscrete subset of `U`. -/
theorem MeromorphicOn.ne_zero_mem_codiscreteWithin {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {f : 𝕜 → E} (hf : MeromorphicOn f U)
    (h'f : ∀ x ∈ U, meromorphicOrderAt f x ≠ ⊤) :
    {x | f x ≠ 0} ∈ codiscreteWithin U := by
  rw [mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf x hx)).1 (h'f x hx)]
    with y hy
  simp [hy]

/-- The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`,
the logarithmic derivative of a product of two meromorphic functions is the sum of the
logarithmic derivatives. -/
theorem MeromorphicOn.logDeriv_mul_eventuallyEq (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (h'f : ∀ x ∈ U, meromorphicOrderAt f x ≠ ⊤) (h'g : ∀ x ∈ U, meromorphicOrderAt g x ≠ ⊤) :
    logDeriv (f * g) =ᶠ[codiscreteWithin U] logDeriv f + logDeriv g := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, hg.analyticAt_mem_codiscreteWithin,
    hf.ne_zero_mem_codiscreteWithin h'f, hg.ne_zero_mem_codiscreteWithin h'g]
    with y h₁y h₂y h₃y h₄y
  rw [Pi.add_apply, Pi.mul_def]
  exact logDeriv_mul y h₃y h₄y h₁y.differentiableAt h₂y.differentiableAt

/-- The logarithmic derivative converts products into sums: away from a codiscrete subset of `ℂ`,
the logarithmic derivative of a product of two meromorphic functions is the sum of the
logarithmic derivatives. -/
theorem Meromorphic.logDeriv_mul_eventuallyEq (hf : Meromorphic f) (hg : Meromorphic g)
    (h'f : ∀ x, meromorphicOrderAt f x ≠ ⊤) (h'g : ∀ x, meromorphicOrderAt g x ≠ ⊤) :
    logDeriv (f * g) =ᶠ[codiscrete 𝕜] logDeriv f + logDeriv g :=
  (meromorphicOn_univ.2 hf).logDeriv_mul_eventuallyEq (meromorphicOn_univ.2 hg)
    (fun x _ ↦ h'f x) (fun x _ ↦ h'g x)

/-- The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`,
the logarithmic derivative of a finite product of meromorphic functions is the sum of the
logarithmic derivatives. -/
theorem logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜'}
    (h : ∀ i ∈ s, MeromorphicOn (F i) U)
    (h' : ∀ i ∈ s, ∀ x ∈ U, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ i ∈ s, F i) =ᶠ[codiscreteWithin U] ∑ i ∈ s, logDeriv (F i) := by
  have hA : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ s, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset s).2 fun i hi ↦ (h i hi).analyticAt_mem_codiscreteWithin
  have hN : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ s, F i y ≠ 0 :=
    (eventually_all_finset s).2 fun i hi ↦ (h i hi).ne_zero_mem_codiscreteWithin (h' i hi)
  filter_upwards [hA, hN] with y h₁y h₂y
  rw [Finset.sum_apply,
    show (∏ i ∈ s, F i) = (∏ i ∈ s, F i ·) from funext fun z ↦ Finset.prod_apply z s F]
  exact logDeriv_prod h₂y fun i hi ↦ (h₁y i hi).differentiableAt

/-- The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`,
the logarithmic derivative of a finite product of meromorphic functions is the sum of the
logarithmic derivatives. -/
theorem logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'}
    (hF : (mulSupport F).Finite)
    (h : ∀ i, MeromorphicOn (F i) U)
    (h' : ∀ i, ∀ x ∈ U, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i) =ᶠ[codiscreteWithin U] ∑ᶠ i, logDeriv (F i) := by
  have hsub : support (fun i ↦ logDeriv (F i)) ⊆ hF.toFinset := by
    intro i hi
    simp only [Finite.coe_toFinset, mem_mulSupport]
    intro h₁i
    apply hi
    change logDeriv (F i) = 0
    rw [h₁i, Pi.one_def, logDeriv_const]
  rw [finprod_eq_prod_of_mulSupport_subset F (s := hF.toFinset) (by simp),
    finsum_eq_sum_of_support_subset _ hsub]
  exact logDeriv_prod_eventuallyEq (fun i _ ↦ h i) fun i _ ↦ h' i

/-- Away from a codiscrete subset of `U`, the logarithmic derivative of the `n`-th power of a
meromorphic function is `n` times the logarithmic derivative. -/
theorem MeromorphicOn.logDeriv_zpow_eventuallyEq (hf : MeromorphicOn f U) (n : ℤ) :
    logDeriv (f ^ n) =ᶠ[codiscreteWithin U] n • logDeriv f := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with y hy
  rw [Pi.smul_apply, zsmul_eq_mul, show f ^ n = (f · ^ n) from rfl]
  exact logDeriv_fun_zpow hy.differentiableAt n

/-- The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`,
the logarithmic derivative of a finite product of integer powers of meromorphic functions is the
corresponding weighted sum of logarithmic derivatives. This is the shape of statement used in the
differentiated Poisson–Jensen formula, where the exponents are given by a divisor. -/
theorem logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'} {d : ι → ℤ}
    (hd : (support d).Finite)
    (h : ∀ i, MeromorphicOn (F i) U)
    (h' : ∀ i, ∀ x ∈ U, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i ^ d i)
      =ᶠ[codiscreteWithin U] fun z ↦ ∑ᶠ i, d i • logDeriv (F i) z := by
  have hA : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ hd.toFinset, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset hd.toFinset).2 fun i _ ↦ (h i).analyticAt_mem_codiscreteWithin
  have hN : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ hd.toFinset, F i y ≠ 0 :=
    (eventually_all_finset hd.toFinset).2 fun i _ ↦ (h i).ne_zero_mem_codiscreteWithin (h' i)
  filter_upwards [hA, hN] with y h₁y h₂y
  have h₀ : ∏ᶠ i, F i ^ d i = ∏ i ∈ hd.toFinset, F i ^ d i := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro i hi
    simp only [mem_mulSupport] at hi
    simp only [Finite.coe_toFinset, mem_support]
    intro h₁i
    exact hi (by rw [h₁i, zpow_zero])
  have hsub : support (fun i ↦ d i • logDeriv (F i) y) ⊆ hd.toFinset := by
    intro i hi
    simp only [Finite.coe_toFinset, mem_support]
    intro h₁i
    apply hi
    change d i • logDeriv (F i) y = 0
    rw [h₁i, zero_zsmul]
  calc logDeriv (∏ᶠ i, F i ^ d i) y
      = logDeriv (fun z ↦ ∏ i ∈ hd.toFinset, (F i ^ d i) z) y := by
        rw [h₀.trans (funext fun z ↦ Finset.prod_apply z hd.toFinset _)]
    _ = ∑ i ∈ hd.toFinset, logDeriv (F i ^ d i) y :=
        logDeriv_prod (fun i hi ↦ zpow_ne_zero _ (h₂y i hi))
          (fun i hi ↦ ((h₁y i hi).zpow (h₂y i hi)).differentiableAt)
    _ = ∑ i ∈ hd.toFinset, d i • logDeriv (F i) y := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [zsmul_eq_mul, show F i ^ d i = (F i · ^ d i) from rfl]
        exact logDeriv_fun_zpow (h₁y i hi).differentiableAt (d i)
    _ = ∑ᶠ i, d i • logDeriv (F i) y := (finsum_eq_sum_of_support_subset _ hsub).symm
