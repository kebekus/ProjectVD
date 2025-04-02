/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import VD.ToMathlib.Divisor_add

open MeromorphicOn Metric Real

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-!
# The Counting Function of a Meromorphic Function

For nontrivially normed fields `𝕜`, this file defines the logarithmic counting
function of a meromorphic function defined on `𝕜`, as used in Value
Distribution Theory.

The counting function of a meromorphic function `f` is a logarithmically
weighted measure of the number of times the function `f` takes a given value `a`
within the disk `∣z∣ ≤ r`, counting multiplicities.  See Section~VI.1 of [Lang:
Introduction to Complex Hyperbolic
Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1) or Section~1.1
of [Noguchi-Winkelmann: Nevanlinna Theory in Several Complex Variables and
Diophantine
Approximation](https://link.springer.com/book/10.1007/978-4-431-54571-2) for a
detailed discussion.

We define the logarithmic counting function first for function with locally
finite support on `𝕜` and then specialize to the setting where the function
with locally finite support is the pole or zero-divisor of a meromorphic
function.
-/

/-!
## Supporting Notation
-/

namespace Function.locallyFinsuppWithin

/--
Shorthand notation for the restriction of a function with locally finite support
within ⊤ to the closed unit ball of radius `r`.
-/
noncomputable def toBall (r : ℝ) :
    locallyFinsuppWithin (⊤ : Set 𝕜) ℤ →+ locallyFinsuppWithin (closedBall (0 : 𝕜) |r|) ℤ := by
  apply restrictMonoidHom
  tauto

/--
Restriction commutes with subtraction.
-/
lemma toBall_sub
    {D₁ D₂ : locallyFinsuppWithin (⊤ : Set 𝕜) ℤ} {r : ℝ} :
    (D₁ - D₂).toBall r = D₁.toBall r - D₂.toBall r := by
  simp

/-!
## The Logarithmic Counting Function of a Function with Locally Finite Support
-/

/--
Definition of the logarithmic counting function for a function with locally
finite support within `⊤`.
-/
noncomputable def logCounting [ProperSpace 𝕜] :
    locallyFinsuppWithin (⊤ : Set 𝕜) ℤ →+ (ℝ → ℝ) where
  toFun D := fun r ↦ ∑ᶠ z, D.toBall r z * log (r * ‖z‖⁻¹) + (D 0) * log r
  map_zero' := by
    simp
    rfl
  map_add' D₁ D₂ := by
    simp only [Set.top_eq_univ, map_add, coe_add, Pi.add_apply, Int.cast_add]
    ext r
    have {A B C D : ℝ} : A + B + (C + D) = A + C + (B + D) := by ring
    rw [Pi.add_apply, this]
    congr 1
    · have h₁s : ((D₁.toBall r).support ∪ (D₂.toBall r).support).Finite := by
        apply Set.finite_union.2
        constructor
        <;> apply finiteSupport _ (isCompact_closedBall 0 |r|)
      repeat
        rw [finsum_eq_sum_of_support_subset (s := h₁s.toFinset)]
      simp_rw [← Finset.sum_add_distrib, ← add_mul]
      --
      intro x hx
      simp_all
      --
      intro x hx
      simp_all
      --
      intro x hx
      by_contra hCon
      simp_all
    · ring

/-- The value of the counting function at zero is zero. -/
@[simp] lemma logCounting_eval_zero [ProperSpace 𝕜]
    (D : locallyFinsuppWithin (⊤ : Set 𝕜) ℤ) :
    logCounting D 0 = 0 := by
  rw [logCounting]
  simp

end Function.locallyFinsuppWithin

/-!
## The Logarithmic Counting Function of a Meromorphic Function
-/

namespace VD

variable [ProperSpace 𝕜]

/-- The logarithmic counting function of a meromorphic function. -/
noncomputable def logCounting (f : 𝕜 → E) (a : WithTop E) :
    ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact (divisor f ⊤)⁻.logCounting
  · exact (divisor (fun z ↦ f z - a.untop₀) ⊤)⁺.logCounting

lemma logCounting_finite {f : 𝕜 → E} {a : E} :
    logCounting f a = (divisor (fun z ↦ f z - a) ⊤)⁺.logCounting := by
  simp [logCounting]

lemma logCounting_finite_eq_logCounting_zero_of_shifted {f : 𝕜 → E} {a : E} :
    logCounting f a = logCounting (f - fun _ ↦ a) 0 := by
  simp [logCounting]

lemma logCounting_zero {f : 𝕜 → E} :
    logCounting f 0 = (divisor f ⊤)⁺.logCounting := by
  simp [logCounting]

lemma logCounting_top {f : 𝕜 → E} :
    logCounting f ⊤ = (divisor f ⊤)⁻.logCounting := by
  simp [logCounting]

lemma logCounting_eval_zero {f : 𝕜 → E} {a : WithTop E}:
    logCounting f a 0 = 0 := by
  by_cases h : a = ⊤ <;> simp [h, logCounting]

theorem log_counting_zero_sub_logCounting_top {f : 𝕜 → E} :
    (divisor f ⊤).logCounting = logCounting f 0 - logCounting f ⊤ := by
  simp [logCounting_zero, logCounting_top]
  nth_rw 1 [← posPart_sub_negPart (divisor f Set.univ)]
  conv =>
    left
    rw [Function.locallyFinsuppWithin.logCounting.map_sub (divisor f Set.univ)⁺ (divisor f Set.univ)⁻]

  simp
  simp_rw [← Function.locallyFinsuppWithin.logCounting.map_sub]

/-!
## Elementary Properties of the Counting Function
-/

theorem logCounting_inv [CompleteSpace 𝕜] {f : 𝕜 → 𝕜} :
    logCounting f 0 = logCounting f⁻¹ ⊤ := by
  simp [logCounting_zero, logCounting_top]

theorem logCounting_add_analytic {f g : 𝕜 → E} (hf : MeromorphicOn f ⊤)
    (hg : AnalyticOn 𝕜 g ⊤) :
    logCounting (f + g) ⊤ = logCounting f ⊤ := by
  simp only [logCounting, ↓reduceDIte,
    hf.divisor_add_analytic (isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg)]

theorem logCounting_add_const {f : 𝕜 → E} {a : E} (hf : MeromorphicOn f ⊤) :
    logCounting (f + fun _ ↦ a) ⊤ = logCounting f ⊤ := by
  apply logCounting_add_analytic hf analyticOn_const

theorem logCounting_sub_const {f : 𝕜 → E} {a : E} (hf : MeromorphicOn f ⊤) :
    logCounting (f - fun _ ↦ a) ⊤ = logCounting f ⊤ := by
  have : f - (fun x ↦ a) = f + fun x ↦ -a := by
    funext x
    simp [sub_eq_add_neg]
  rw [this]
  apply logCounting_add_analytic hf analyticOn_const

end VD
