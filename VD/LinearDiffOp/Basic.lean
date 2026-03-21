/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Linear Differential Operators

This file defines linear differential operators, as maps between function spaces
that depend only on (higher) derivatives. In a nutshell, a linear differential
operator of order ≤ n is a map `(D : Functions → Function)` such that `D f x` is
a linear function of the tuple (f x, f' x, f'' x, … up to order n)`.

## TODO

- Algebra structure of differential operators over the ring of functions

- Composition of differentials operators

- Notion of "n times continuously differentiable differential operator", loss of
  regularity when applying the operator.

- Leibniz rule
-/
open Filter Function Metric Real Set Classical Topology

set_option backward.isDefEq.respectTransparency false

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  {s : Set E} {e : E} {n : ℕ} {f₁ f₂ : E → F}
  {ι : Type*} {φ : ι → E → F} {I : Finset ι}

noncomputable section

/-!
## Definition and Application to Functions
-/

variable (𝕜 E F G) in
/--
**Linear differential operator of order ≤ n** Given normed vector spaces `E`,
`F` and `G` and a number `n`, we define a linear differential operator as a map
("tensor field") from `E` into linear maps from tuples `(E [0]→L[𝕜] F, …, E
[n]→L[𝕜] F)` to `G`. The instance `CoeFun` below defines how this.
-/
@[ext]
structure LinearDiffOp (n) where
  tensorField : E → (∀ i : Fin (n + 1), E [×i]→L[𝕜] F) →L[𝕜] G

/--
**Application of linear differential operators to functions** Given a
differential operator `D : LinearDiffOp 𝕜 E F G n` and a function `f : E → F`,
construct a function `D f : E → G` by applying the tensor field of `D` to the
Taylor series of `f`.
-/
@[coe] def LinearDiffOp.apply {n} (D : LinearDiffOp 𝕜 E F G n) (f : E → F) :
    E → G := fun e ↦ D.tensorField e ((ftaylorSeries 𝕜 f e) ·)

/--
Definition of the operation defined by linear differential operators on
functions.
-/
theorem linearDiffOp_apply (D : LinearDiffOp 𝕜 E F G n) (f : E → F) :
    D.apply f = fun e ↦ D.tensorField e ((ftaylorSeries 𝕜 f e) ·) := rfl

/--
Establish linear differential operators as instance of `CoeFun`, mapping maps `E
→ F` to `E → G`. This allows writing `D f` as a shorthand for `D.apply f`.

NOTE: In typical scenarios, the coercion will not be injective. This is because
not every tensor field appears as the truncated taylor series of a function. The
multilinear maps appearing in taylor series practise are symmetric,
-/
instance (n : ℕ) : CoeFun (LinearDiffOp 𝕜 E F G n) fun _ ↦ (E → F) → (E → G) where
  coe (D f) := D.apply f

/--
Definition of the operation defined by linear differential operators on
functions.
-/
theorem linearDiffOp_coe_apply (D : LinearDiffOp 𝕜 E F G n) (f : E → F) :
    D f = fun e ↦ D.tensorField e ((ftaylorSeries 𝕜 f e) ·) := rfl

/--
**Application of linear differential operators to functions within a set** Given
a differential operator `D : LinearDiffOp 𝕜 E F G n`, a set `s : Set E` and a
function `f : E → F`, construct a function `D f : E → G` by applying the tensor
field of `D` to the Taylor series of `f` within `s`.
-/
def LinearDiffOp.applyWithin (D : LinearDiffOp 𝕜 E F G n) (s : Set E) (f : E → F) :
    E → G := fun e ↦ D.tensorField e ((ftaylorSeriesWithin 𝕜 f s e) ·)

/--
Definition of the operation defined by linear differential operators on
functions within a set.
-/
theorem linearDiffOp_applyWithin (D : LinearDiffOp 𝕜 E F G n) (f : E → F) :
    D.applyWithin s f = fun e ↦ D.tensorField e ((ftaylorSeriesWithin 𝕜 f s e) ·) := rfl

/-!
## Elementary Properties: Locality
-/

/--
Linear differential operators are local.
-/
lemma Filter.EventuallyEq.linearDiffOp_apply (D : LinearDiffOp 𝕜 E F G n)
    (h : f₁ =ᶠ[𝓝 e] f₂) :
    D f₁ =ᶠ[𝓝 e] D f₂ := by
  filter_upwards [h.ftaylorSeries 𝕜] with e₁ he₁
  simp [_root_.linearDiffOp_coe_apply, he₁]

/--
Linear differential operators are local.
-/
lemma Filter.EventuallyEqWithin.linearDiffOp_applyWithin (D : LinearDiffOp 𝕜 E F G n)
    (h : f₁ =ᶠ[𝓝[s] e] f₂) :
    D.applyWithin s f₁ =ᶠ[𝓝[s] e] D.applyWithin s f₂ := by
  filter_upwards [h.ftaylorSeriesWithin 𝕜] with e₁ he₁
  simp [_root_.linearDiffOp_applyWithin, he₁]

/-!
## Elementary Properties: Linearity of Application for Sufficiently Regular Functions
-/

/--
For sufficiently regular functions, linear differential operators commute with addition.
-/
@[to_fun] lemma linearDiffOp_apply_add (h₁ : ContDiffAt 𝕜 n f₁ e) (h₂ : ContDiffAt 𝕜 n f₂ e)
    (D : LinearDiffOp 𝕜 E F G n) :
    D (f₁ + f₂) e = D f₁ e + D f₂ e := by
  have : (fun (x : Fin (n + 1)) ↦ ftaylorSeries 𝕜 (f₁ + f₂) e x)
      = (fun (x : Fin (n + 1)) ↦ ftaylorSeries 𝕜 f₁ e x)
        + (fun (x : Fin (n + 1)) ↦ ftaylorSeries 𝕜 f₂ e x) := by
    ext m v
    unfold ftaylorSeries
    rw [iteratedFDeriv_add_apply (h₁.of_le (by norm_cast; grind))
      (h₂.of_le (by norm_cast; grind)), Pi.add_apply]
  simp_all [linearDiffOp_coe_apply]

/--
For sufficiently regular functions, linear differential operators commute with addition.
-/
@[to_fun] lemma linearDiffOp_applyWithin_add (hs : UniqueDiffOn 𝕜 s) (he : e ∈ s)
    (h₁ : ContDiffWithinAt 𝕜 n f₁ s e) (h₂ : ContDiffWithinAt 𝕜 n f₂ s e)  (D : LinearDiffOp 𝕜 E F G n) :
    D.applyWithin s (f₁ + f₂) e = D.applyWithin s f₁ e + D.applyWithin s f₂ e := by
  have : (fun (x : Fin (n + 1)) ↦ ftaylorSeriesWithin 𝕜 (f₁ + f₂) s e x)
      = (fun (x : Fin (n + 1)) ↦ ftaylorSeriesWithin 𝕜 f₁ s e x)
        + (fun (x : Fin (n + 1)) ↦ ftaylorSeriesWithin 𝕜 f₂ s e x) := by
    ext m v
    unfold ftaylorSeriesWithin
    rw [iteratedFDerivWithin_add_apply (h₁.of_le (by norm_cast; grind))
      (h₂.of_le (by norm_cast; grind)) hs he, Pi.add_apply]
  simp_all [linearDiffOp_applyWithin]

/--
For sufficiently regular functions, linear differential operators commute with sums.
-/
@[to_fun] lemma linearDiffOp_apply_sum (h : ∀ i ∈ I, ContDiffAt 𝕜 n (φ i) e)
    (D : LinearDiffOp 𝕜 E F G n) :
    D (∑ i ∈ I, φ i) e = ∑ i ∈ I, D (φ i) e := by
  have : (fun (x : Fin (n + 1)) ↦ ftaylorSeries 𝕜 (∑ i ∈ I, φ i) e x)
      = ∑ i ∈ I, (fun (x : Fin (n + 1)) ↦ ftaylorSeries 𝕜 (φ i) e x) := by
    ext m v
    unfold ftaylorSeries
    rw [iteratedFDeriv_sum_apply]
    simp only [ContinuousMultilinearMap.sum_apply, Finset.sum_apply]
    exact fun j hj ↦ (h j hj).of_le (by norm_num; grind)
  simp_all [linearDiffOp_coe_apply]

/--
For sufficiently regular functions, linear differential operators commute with sums.
-/
@[to_fun] lemma linearDiffOp_applyWithin_sum  (hs : UniqueDiffOn 𝕜 s) (he : e ∈ s)
    (h : ∀ i ∈ I, ContDiffWithinAt 𝕜 n (φ i) s e) (D : LinearDiffOp 𝕜 E F G n) :
    D.applyWithin s (∑ i ∈ I, φ i) e = ∑ i ∈ I, D.applyWithin s (φ i) e := by
  have : (fun (x : Fin (n + 1)) ↦ ftaylorSeriesWithin 𝕜 (∑ i ∈ I, φ i) s e x)
      = ∑ i ∈ I, (fun (x : Fin (n + 1)) ↦ ftaylorSeriesWithin 𝕜 (φ i) s e x) := by
    ext m v
    unfold ftaylorSeriesWithin
    rw [iteratedFDerivWithin_sum_apply hs he]
    simp only [ContinuousMultilinearMap.sum_apply, Finset.sum_apply]
    exact fun j hj ↦ (h j hj).of_le (by norm_num; grind)
  simp_all [linearDiffOp_applyWithin]

/--
For sufficiently regular functions, linear differential operators commute with subtraction.
-/
@[to_fun] lemma linearDiffOp_apply_sub (h₁ : ContDiffAt 𝕜 n f₁ e) (h₂ : ContDiffAt 𝕜 n f₂ e)
    (D : LinearDiffOp 𝕜 E F G n) :
    D (f₁ - f₂) e = D f₁ e - D f₂ e := by
  have : (fun (x : Fin (n + 1)) ↦ ftaylorSeries 𝕜 (f₁ - f₂) e x)
      = (fun (x : Fin (n + 1)) ↦ ftaylorSeries 𝕜 f₁ e x)
        - (fun (x : Fin (n + 1)) ↦ ftaylorSeries 𝕜 f₂ e x) := by
    ext m v
    unfold ftaylorSeries
    rw [iteratedFDeriv_sub_apply (h₁.of_le (by norm_cast; grind))
      (h₂.of_le (by norm_cast; grind)), Pi.sub_apply]
  simp_all [_root_.linearDiffOp_coe_apply]

/--
For sufficiently regular functions, linear Differential operators commute with subtraction.
-/
@[to_fun] lemma linearDiffOp_applyWithin_sub (hs : UniqueDiffOn 𝕜 s) (he : e ∈ s)
    (h₁ : ContDiffWithinAt 𝕜 n f₁ s e) (h₂ : ContDiffWithinAt 𝕜 n f₂ s e)
    (D : LinearDiffOp 𝕜 E F G n) :
    D.applyWithin s (f₁ - f₂) e = D.applyWithin s f₁ e - D.applyWithin s f₂ e := by
  have : (fun (x : Fin (n + 1)) ↦ ftaylorSeriesWithin 𝕜 (f₁ - f₂) s e x)
      = (fun (x : Fin (n + 1)) ↦ ftaylorSeriesWithin 𝕜 f₁ s e x)
        - (fun (x : Fin (n + 1)) ↦ ftaylorSeriesWithin 𝕜 f₂ s e x) := by
    ext m v
    unfold ftaylorSeriesWithin
    rw [iteratedFDerivWithin_sub_apply (h₁.of_le (by norm_cast; grind))
      (h₂.of_le (by norm_cast; grind)) hs he, Pi.sub_apply]
  simp_all [linearDiffOp_applyWithin]

/--
Linear differential operators commute with negation.
-/
@[to_fun] lemma linearDiffOp_apply_neg {f : E → F} (D : LinearDiffOp 𝕜 E F G n) :
    D (-f) e = -(D f e) := by
  have : (fun (x : Fin (n + 1)) ↦ ftaylorSeries 𝕜 (-f) e x)
      = - (fun (x : Fin (n + 1)) ↦ ftaylorSeries 𝕜 f e x) := by
    ext m v
    unfold ftaylorSeries
    simp [iteratedFDeriv_neg_apply]
  simp_all [_root_.linearDiffOp_coe_apply]

/--
Linear differential operators commute with negation.
-/
@[to_fun] lemma linearDiffOp_applyWithin_neg {f : E → F} (hs : UniqueDiffOn 𝕜 s) (he : e ∈ s)
    (D : LinearDiffOp 𝕜 E F G n) :
    D.applyWithin s (-f) e = -(D.applyWithin s f e) := by
  have : (fun (x : Fin (n + 1)) ↦ ftaylorSeriesWithin 𝕜 (-f) s e x)
      = - (fun (x : Fin (n + 1)) ↦ ftaylorSeriesWithin 𝕜 f s e x) := by
    ext m v
    unfold ftaylorSeriesWithin
    simp [iteratedFDerivWithin_neg_apply hs he]
  simp_all [linearDiffOp_applyWithin]

/--
For sufficiently regular functions, linear Differential operators commute with scalar multiplication.

TODO: Check if regularity is actually used.
-/
@[simp, to_fun] lemma linearDiffOp_apply_const_smul {μ : 𝕜} {f : E → F} (h : ContDiffAt 𝕜 n f e)
    (D : LinearDiffOp 𝕜 E F G n) :
    D (μ • f) e = μ • D f e := by
  have : (fun (x : Fin (n + 1)) ↦ ftaylorSeries 𝕜 (μ • f) e ↑x)
      = μ • (fun (x : Fin (n + 1)) ↦ ftaylorSeries 𝕜 f e ↑x) := by
    ext m v
    unfold ftaylorSeries
    rw [iteratedFDeriv_const_smul_apply (h.of_le (by norm_cast; grind)), Pi.smul_apply]
  simp_all [_root_.linearDiffOp_coe_apply]

/--
For sufficiently regular functions, linear Differential operators commute with scalar multiplication.

TODO: Check if regularity is actually used.
-/
@[simp, to_fun] lemma linearDiffOp_applyWithin_const_smul {μ : 𝕜} {f : E → F} (hs : UniqueDiffOn 𝕜 s) (he : e ∈ s)
    (h : ContDiffWithinAt 𝕜 n f s e) (D : LinearDiffOp 𝕜 E F G n) :
    D.applyWithin s (μ • f) e = μ • D.applyWithin s f e := by
  have : (fun (x : Fin (n + 1)) ↦ ftaylorSeriesWithin 𝕜 (μ • f) s e ↑x)
      = μ • (fun (x : Fin (n + 1)) ↦ ftaylorSeriesWithin 𝕜 f s e ↑x) := by
    ext m v
    unfold ftaylorSeriesWithin
    rw [iteratedFDerivWithin_const_smul_apply (h.of_le (by norm_cast; grind)) hs he, Pi.smul_apply]
  simp_all [linearDiffOp_applyWithin]

/--
Linear differential operators map zero to zero.
-/
@[simp, to_fun] lemma linearDiffOp_apply_zero (D : LinearDiffOp 𝕜 E F G n) :
    D 0 e = 0 := by
  rw [linearDiffOp_coe_apply]
  simp only [ftaylorSeries_zero, Pi.zero_apply, FormalMultilinearSeries.zero_apply]
  exact (D.tensorField e).map_zero

/--
Linear differential operators map zero to zero.
-/
@[simp, to_fun] lemma linearDiffOp_applyWithin_zero (D : LinearDiffOp 𝕜 E F G n) :
    D.applyWithin s 0 e = 0 := by
  rw [linearDiffOp_applyWithin]
  simp only [ftaylorSeriesWithin_zero, Pi.zero_apply, FormalMultilinearSeries.zero_apply]
  exact (D.tensorField e).map_zero
