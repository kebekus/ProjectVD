/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Coprime.Basic
public import VD.AlgebraicDependence.GrowthField

/-!
# Valiron–Mohon'ko for Rational Functions — Algebraic Dependence work package G

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §9.

Mathlib target: follows the germ field `VD/Field/` upstream. Dependencies: package F, the
pointwise Bezout estimate `Real.nsmul_posLog_norm_add_posLog_norm_inv_le_of_bezout` of
package A (G2), and the divisor estimate B3 proved here at the level of germs.

Throughout, `K := MeromorphicOn.germRing ℂ Set.univ` is the field of meromorphic germs on `ℂ`,
`F := growthField hG` is the growth field of a growth class `G`, `P Q : F[X]`, and
`aeval a P / aeval a Q` is the rational function `P/Q` evaluated at a germ `a`.

## Main results

- B3, `MeromorphicOn.GermRing.nsmul_negPart_divisor_add_posPart_divisor_le_of_bezout`: the
  **divisor estimate** for a quotient of monic polynomial expressions with a Bezout
  certificate, `(p - q) • (div a)⁻ + (div Q(a))⁺ ≤ (div (P(a)/Q(a)))⁻ + C • (small divisors)`.
- G1, `MeromorphicOn.GermRing.characteristic_aeval_div_le`: the **upper bound**
  `T(r, P(a)/Q(a)) ≤ max (deg P) (deg Q) · T(r, a) + u(r)`, `u ∈ G`, by induction along the
  Euclidean algorithm. No coprimality is needed.
- G3, `MeromorphicOn.GermRing.nsmul_characteristic_le_characteristic_aeval_div`: the **lower
  bound** `max (deg P) (deg Q) · T(r, a) ≤ T(r, P(a)/Q(a)) + u(r)` for coprime `P, Q`, from the
  integrated Bezout estimates.
- T8, `MeromorphicOn.GermRing.exists_abs_characteristic_aeval_div_sub_le`: the
  **Valiron–Mohon'ko identity** `T(r, R(a)) = deg R · T(r, a) + u(r)` with `u ∈ G`, for
  `R = P/Q` with coprime numerator and denominator in `F[X]`.
- T9, `MeromorphicOn.GermRing.characteristic_aeval_div_sub_isLittleO`: the classical form,
  `T(r, R(f)) = deg R · T(r, f) + o(T(r, f))` for `R` with coefficients in the field of small
  functions `S(f)` (Laine, Theorem 2.2.5).

## Implementation notes

The lower bound is where the factor `max (deg P) (deg Q)` has to be won; the naive routes
(triangle inequality along the Euclidean algorithm, or the algebraic dependence bound applied
to `P(a) - g Q(a) = 0`) lose it (plan §1, decision 6). Following Mohon'ko, the proof first
reduces to monic `P, Q` with `1 ≤ deg Q ≤ deg P`, then proves
`(p - q) T(r, a) + T(r, 1/Q(a)) ≤ T(r, P(a)/Q(a)) + small` separately for the proximity
functions (pointwise estimate G2, integrated on a codiscrete subset of the circle) and the
counting functions (divisor estimate B3, a valuation-theoretic case analysis at each point), and
concludes with `T(r, 1/Q(a)) = T(r, Q(a)) + O(1) = q T(r, a) + small`.

All "small" terms are sums of characteristics of coefficients of `P`, `Q` and of the Bezout
cofactors `U`, `V`; these lie in the growth field, so the sums lie in `G`. The case where `a`
itself lies in the growth field (so that `P(a)` or `Q(a)` may vanish) is dispatched separately:
then `P(a)/Q(a)` lies in the growth field as well, and both sides are small.
-/

@[expose] public section

open Asymptotics Filter Finset Function Polynomial Real Set Topology

namespace MeromorphicOn.GermRing

/-!
## Representatives of Polynomial Expressions
-/

section Representatives

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜}

/-- The chosen representative of a monic polynomial expression in germs agrees with the monic
polynomial expression in the chosen representatives along `codiscreteWithin U`. -/
theorem out_monic (a : germRing 𝕜 U) (c : ℕ → germRing 𝕜 U) (p : ℕ) :
    out (a ^ p + ∑ j ∈ range p, c j * a ^ j)
      =ᶠ[codiscreteWithin U] out a ^ p + ∑ j ∈ range p, out (c j) * out a ^ j :=
  (out_add _ _).trans ((out_pow a p).add ((out_sum _ _).trans
    (EventuallyEq.finset_sum fun j _ ↦ (out_mul _ _).trans
      ((EventuallyEq.refl _ _).mul (out_pow a j)))))

/-- The chosen representative of a polynomial expression in germs agrees with the polynomial
expression in the chosen representatives along `codiscreteWithin U`. -/
theorem out_sum_mul_pow (a : germRing 𝕜 U) (c : ℕ → germRing 𝕜 U) (s : Finset ℕ) :
    out (∑ j ∈ s, c j * a ^ j) =ᶠ[codiscreteWithin U] ∑ j ∈ s, out (c j) * out a ^ j :=
  (out_sum _ _).trans (EventuallyEq.finset_sum fun j _ ↦ (out_mul _ _).trans
    ((EventuallyEq.refl _ _).mul (out_pow a j)))

theorem out_div (a b : germRing 𝕜 U) : out (a / b) =ᶠ[codiscreteWithin U] out a / out b := by
  rw [div_eq_mul_inv]
  filter_upwards [out_mul a b⁻¹, out_inv b] with z h₁ h₂
  rw [h₁, Pi.mul_apply, h₂, Pi.inv_apply, Pi.div_apply, _root_.div_eq_mul_inv]

end Representatives

/-!
## The Divisor Estimate (B3)

At the level of germs, `orderAt · z` is a valuation on the field of germs, and the divisor of a
germ at `z ∈ U` is `(orderAt a z).untop₀`. The divisor estimate for a quotient `P(a)/Q(a)` of
monic polynomial expressions with a Bezout certificate `U(a) P(a) + V(a) Q(a) = 1` is a case
analysis in this valuation.
-/

section Divisor

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} [h₁U : Fact (IsPreconnected U)]
  [h₂U : Fact U.Nontrivial] {z : 𝕜}

omit h₁U h₂U in
/-- The divisor of a germ, evaluated at a point of `U`. -/
theorem divisor_apply (a : germRing 𝕜 U) (hz : z ∈ U) : divisor a z = (orderAt a z).untop₀ :=
  MeromorphicOn.divisor_apply (meromorphicOn_out a) hz

/-- In `WithTop ℤ`, an element whose `untop₀` has negative part at most `s` is at least `-s`. -/
private lemma neg_le_of_negPart_untop₀_le {y : WithTop ℤ} {s : ℤ} (h : (y.untop₀)⁻ ≤ s) :
    ((-s : ℤ) : WithTop ℤ) ≤ y := by
  cases y with
  | top => exact le_top
  | coe k =>
    rw [WithTop.untop₀_coe] at h
    exact WithTop.coe_le_coe.2 (by linarith [neg_le_negPart k])

/-- Lower bound for the order of a polynomial expression `Σ_{i∈s} x i * a ^ i` at `z`: if all
coefficients have order at least `-t` and all exponents are at most `e`, the order is at least
`-t - e · (ord a)⁻`. -/
lemma le_orderAt_sum_mul_pow (hz : z ∈ U) {a : germRing 𝕜 U} {x : ℕ → germRing 𝕜 U}
    {s : Finset ℕ} {e : ℕ} {t ν : ℤ} (hν : orderAt a z = ν) (he : ∀ i ∈ s, i ≤ e)
    (hx : ∀ i ∈ s, ((-t : ℤ) : WithTop ℤ) ≤ orderAt (x i) z) :
    ((-t - e * ν⁻ : ℤ) : WithTop ℤ) ≤ orderAt (∑ i ∈ s, x i * a ^ i) z := by
  have hU : Preperfect U := h₁U.out.preperfect_of_nontrivial h₂U.out
  refine le_orderAt_sum hU hz fun i hi ↦ ?_
  rw [orderAt_mul hU hz, orderAt_pow hU hz, hν]
  cases hxi : orderAt (x i) z with
  | top => simp
  | coe y =>
    have hy : -t ≤ y := WithTop.coe_le_coe.1 (hxi ▸ hx i hi)
    have hie : (i : ℤ) ≤ e := by exact_mod_cast he i hi
    have h₁ : -(i : ℤ) * ν⁻ ≤ i * ν := by nlinarith [neg_le_negPart ν]
    have h₂ : -(e : ℤ) * ν⁻ ≤ -(i : ℤ) * ν⁻ := by nlinarith [negPart_nonneg ν]
    exact_mod_cast (by linarith : -t - e * ν⁻ ≤ y + i * ν)

/--
**Divisor estimate for a quotient with a Bezout certificate** (B3). Let
`P(a) = a ^ p + Σ_{j<p} c j * a ^ j` and `Q(a) = a ^ q + Σ_{k<q} b k * a ^ k` be monic polynomial
expressions of degrees `1 ≤ q ≤ p` in a nonzero germ `a`, both nonzero, and let
`U(a) = Σ_{i≤m} u i * a ^ i`, `V(a) = Σ_{i≤n} v i * a ^ i` satisfy `U(a) P(a) + V(a) Q(a) = 1`.
Then
`(p - q) • (div a)⁻ + (div Q(a))⁺ ≤ (div (P(a)/Q(a)))⁻ + (p + m + n + 1) • D`, where `D` is the
sum of the pole divisors of all coefficients of `P`, `Q`, `U`, `V`.

At a point where the coefficients are regular and `a` has a pole of order `k`, both sides equal
`(p - q) k`; at a point where `a` is regular and `Q(a)` vanishes to order `κ`, the Bezout
identity forces `P(a)` to be regular, so `P(a)/Q(a)` has a pole of order at least `κ`; all other
points are charged to the pole divisors of the coefficients.
-/
theorem nsmul_negPart_divisor_add_posPart_divisor_le_of_bezout {a : germRing 𝕜 U} (ha : a ≠ 0)
    {c b u v : ℕ → germRing 𝕜 U} {p q m n : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p)
    (hP : a ^ p + ∑ j ∈ range p, c j * a ^ j ≠ 0) (hQ : a ^ q + ∑ k ∈ range q, b k * a ^ k ≠ 0)
    (h : (∑ i ∈ range (m + 1), u i * a ^ i) * (a ^ p + ∑ j ∈ range p, c j * a ^ j)
      + (∑ i ∈ range (n + 1), v i * a ^ i) * (a ^ q + ∑ k ∈ range q, b k * a ^ k) = 1) :
    (p - q) • (divisor a)⁻ + (divisor (a ^ q + ∑ k ∈ range q, b k * a ^ k))⁺
      ≤ (divisor ((a ^ p + ∑ j ∈ range p, c j * a ^ j)
          / (a ^ q + ∑ k ∈ range q, b k * a ^ k)))⁻
        + (p + m + n + 1) • (∑ j ∈ range p, (divisor (c j))⁻ + ∑ k ∈ range q, (divisor (b k))⁻
          + ∑ i ∈ range (m + 1), (divisor (u i))⁻ + ∑ i ∈ range (n + 1), (divisor (v i))⁻) := by
  have hU : Preperfect U := h₁U.out.preperfect_of_nontrivial h₂U.out
  set P := a ^ p + ∑ j ∈ range p, c j * a ^ j with hP_def
  set Q := a ^ q + ∑ k ∈ range q, b k * a ^ k with hQ_def
  set Ua := ∑ i ∈ range (m + 1), u i * a ^ i with hUa_def
  set Va := ∑ i ∈ range (n + 1), v i * a ^ i with hVa_def
  rw [locallyFinsuppWithin.le_def]
  intro z
  by_cases hz : z ∈ U
  swap
  · simp [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
  simp only [locallyFinsuppWithin.coe_nsmul, Pi.smul_apply, locallyFinsuppWithin.coe_add,
    Pi.add_apply, locallyFinsuppWithin.negPart_apply, locallyFinsuppWithin.posPart_apply,
    locallyFinsuppWithin.coe_sum, Finset.sum_apply, divisor_apply _ hz]
  simp only [nsmul_eq_mul]
  -- The orders of `a`, `P(a)`, `Q(a)` are integers.
  lift orderAt a z to ℤ using orderAt_ne_top h₁U.out h₂U.out ha hz with ν hν
  lift orderAt P z to ℤ using orderAt_ne_top h₁U.out h₂U.out hP hz with ρ hρ
  lift orderAt Q z to ℤ using orderAt_ne_top h₁U.out h₂U.out hQ hz with κ hκ
  have hg : orderAt (P / Q) z = ((ρ - κ : ℤ) : WithTop ℤ) := by
    rw [div_eq_mul_inv, orderAt_mul hU hz, orderAt_inv hU hz, ← hρ, ← hκ]
    norm_cast
  rw [hg]
  simp only [WithTop.untop₀_coe]
  -- The sum of the pole orders of all coefficients.
  set S₁ := ∑ j ∈ range p, ((orderAt (c j) z).untop₀)⁻ with hS₁
  set S₂ := ∑ k ∈ range q, ((orderAt (b k) z).untop₀)⁻ with hS₂
  set S₃ := ∑ i ∈ range (m + 1), ((orderAt (u i) z).untop₀)⁻ with hS₃
  set S₄ := ∑ i ∈ range (n + 1), ((orderAt (v i) z).untop₀)⁻ with hS₄
  have hS₁₀ : 0 ≤ S₁ := sum_nonneg fun _ _ ↦ negPart_nonneg _
  have hS₂₀ : 0 ≤ S₂ := sum_nonneg fun _ _ ↦ negPart_nonneg _
  have hS₃₀ : 0 ≤ S₃ := sum_nonneg fun _ _ ↦ negPart_nonneg _
  have hS₄₀ : 0 ≤ S₄ := sum_nonneg fun _ _ ↦ negPart_nonneg _
  set s := S₁ + S₂ + S₃ + S₄ with hs
  have hs₀ : 0 ≤ s := by positivity
  -- Every coefficient has order at least `-s`.
  have hc : ∀ j ∈ range p, ((-s : ℤ) : WithTop ℤ) ≤ orderAt (c j) z := by
    intro j hj
    have h₁ : ((orderAt (c j) z).untop₀)⁻ ≤ S₁ := by
      rw [hS₁]
      exact single_le_sum (f := fun i ↦ ((orderAt (c i) z).untop₀)⁻) (fun i _ ↦ negPart_nonneg _) hj
    exact neg_le_of_negPart_untop₀_le (by rw [hs]; linarith)
  have hb : ∀ k ∈ range q, ((-s : ℤ) : WithTop ℤ) ≤ orderAt (b k) z := by
    intro k hk
    have h₁ : ((orderAt (b k) z).untop₀)⁻ ≤ S₂ := by
      rw [hS₂]
      exact single_le_sum (f := fun i ↦ ((orderAt (b i) z).untop₀)⁻) (fun i _ ↦ negPart_nonneg _) hk
    exact neg_le_of_negPart_untop₀_le (by rw [hs]; linarith)
  have hu : ∀ i ∈ range (m + 1), ((-s : ℤ) : WithTop ℤ) ≤ orderAt (u i) z := by
    intro i hi
    have h₁ : ((orderAt (u i) z).untop₀)⁻ ≤ S₃ := by
      rw [hS₃]
      exact single_le_sum (f := fun i ↦ ((orderAt (u i) z).untop₀)⁻) (fun i _ ↦ negPart_nonneg _) hi
    exact neg_le_of_negPart_untop₀_le (by rw [hs]; linarith)
  have hv : ∀ i ∈ range (n + 1), ((-s : ℤ) : WithTop ℤ) ≤ orderAt (v i) z := by
    intro i hi
    have h₁ : ((orderAt (v i) z).untop₀)⁻ ≤ S₄ := by
      rw [hS₄]
      exact single_le_sum (f := fun i ↦ ((orderAt (v i) z).untop₀)⁻) (fun i _ ↦ negPart_nonneg _) hi
    exact neg_le_of_negPart_untop₀_le (by rw [hs]; linarith)
  -- Lower bounds for the orders of the polynomial expressions.
  have hPlow : ((-s - (p - 1 : ℕ) * ν⁻ : ℤ) : WithTop ℤ) ≤ orderAt (∑ j ∈ range p, c j * a ^ j) z :=
    le_orderAt_sum_mul_pow hz hν.symm (fun j hj ↦ Nat.le_sub_one_of_lt (mem_range.1 hj)) hc
  have hQlow : ((-s - (q - 1 : ℕ) * ν⁻ : ℤ) : WithTop ℤ) ≤ orderAt (∑ k ∈ range q, b k * a ^ k) z :=
    le_orderAt_sum_mul_pow hz hν.symm (fun k hk ↦ Nat.le_sub_one_of_lt (mem_range.1 hk)) hb
  have hUlow : ((-s - m * ν⁻ : ℤ) : WithTop ℤ) ≤ orderAt Ua z :=
    le_orderAt_sum_mul_pow hz hν.symm (fun i hi ↦ Nat.lt_succ_iff.1 (mem_range.1 hi)) hu
  have hVlow : ((-s - n * ν⁻ : ℤ) : WithTop ℤ) ≤ orderAt Va z :=
    le_orderAt_sum_mul_pow hz hν.symm (fun i hi ↦ Nat.lt_succ_iff.1 (mem_range.1 hi)) hv
  have hν₀ : 0 ≤ ν⁻ := negPart_nonneg ν
  have hmν : 0 ≤ (m : ℤ) * ν⁻ := by positivity
  have hnν : 0 ≤ (n : ℤ) * ν⁻ := by positivity
  have hρκ₀ : 0 ≤ (ρ - κ)⁻ := negPart_nonneg _
  -- Key estimate from the Bezout identity: `κ⁺ ≤ (ρ - κ)⁻ + s + (m + n) ν⁻`.
  have hkey : κ⁺ ≤ (ρ - κ)⁻ + (s + (m + n) * ν⁻) := by
    rcases le_or_gt κ (s + (m + n) * ν⁻) with hκt | hκt
    · rcases le_or_gt κ 0 with h0 | h0
      · rw [posPart_eq_zero.2 h0]
        linarith
      · rw [posPart_eq_self.2 h0.le]
        linarith
    · -- `Q(a)` vanishes to high order: then `V(a) Q(a)` vanishes and `U(a) P(a)` is a unit.
      have h₁ : (0 : WithTop ℤ) < orderAt (-(Va * Q)) z := by
        rw [orderAt_neg hU hz, orderAt_mul hU hz, ← hκ]
        calc (0 : WithTop ℤ) < ((-s - n * ν⁻ + κ : ℤ) : WithTop ℤ) := by
              exact_mod_cast (by nlinarith : (0 : ℤ) < -s - n * ν⁻ + κ)
          _ = ((-s - n * ν⁻ : ℤ) : WithTop ℤ) + κ := by push_cast; rfl
          _ ≤ orderAt Va z + κ := add_le_add hVlow le_rfl
      have h₂ : orderAt (Ua * P) z = 0 := by
        have : Ua * P = 1 + -(Va * Q) := by rw [← sub_eq_add_neg]; exact eq_sub_of_add_eq h
        rw [this, orderAt_add_eq_left_of_lt hU hz (by rwa [orderAt_one hU hz]), orderAt_one hU hz]
      rw [orderAt_mul hU hz, ← hρ] at h₂
      cases hμ : orderAt Ua z with
      | top =>
        rw [hμ, top_add] at h₂
        exact absurd h₂ WithTop.top_ne_zero
      | coe μ =>
        rw [hμ] at h₂ hUlow
        have h₃ : μ + ρ = 0 := by exact_mod_cast h₂
        have h₄ : -s - m * ν⁻ ≤ μ := WithTop.coe_le_coe.1 hUlow
        have hρκ : ρ - κ ≤ 0 := by linarith
        rw [negPart_eq_neg.2 hρκ, posPart_eq_self.2 (by linarith : 0 ≤ κ)]
        linarith
  have hpq : ((p - q : ℕ) : ℤ) = p - q := by omega
  have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have hqp' : (q : ℤ) ≤ p := by exact_mod_cast hqp
  rw [hpq]
  push_cast
  rcases le_or_gt ν⁻ s with hνs | hνs
  · -- `ν⁻ ≤ s`: everything is bounded by the pole orders of the coefficients.
    have h₁ : ((p : ℤ) - q) * ν⁻ ≤ p * s := by nlinarith
    have h₂ : (m : ℤ) * ν⁻ ≤ m * s := mul_le_mul_of_nonneg_left hνs (by positivity)
    have h₃ : (n : ℤ) * ν⁻ ≤ n * s := mul_le_mul_of_nonneg_left hνs (by positivity)
    linarith
  · -- `ν⁻ > s`: `a` has a pole of order `ν⁻`, and the leading terms dominate.
    have hν0 : ν < 0 := by
      by_contra h0
      rw [negPart_eq_zero.2 (not_lt.1 h0)] at hνs
      exact absurd hνs (not_lt.2 hs₀)
    have hνneg : ν⁻ = -ν := negPart_eq_neg.2 hν0.le
    have hp1 : ((p - 1 : ℕ) : ℤ) = p - 1 := by omega
    have hq1 : ((q - 1 : ℕ) : ℤ) = q - 1 := by omega
    have hρ' : ρ = p * ν := by
      have : orderAt P z = orderAt (a ^ p) z := by
        refine orderAt_add_eq_left_of_lt hU hz (lt_of_lt_of_le ?_ hPlow)
        rw [orderAt_pow hU hz, ← hν, hp1, hνneg]
        exact_mod_cast (by linarith : (p : ℤ) * ν < -s - (p - 1) * -ν)
      rw [← hρ, orderAt_pow hU hz, ← hν] at this
      exact_mod_cast this
    have hκ' : κ = q * ν := by
      have : orderAt Q z = orderAt (a ^ q) z := by
        refine orderAt_add_eq_left_of_lt hU hz (lt_of_lt_of_le ?_ hQlow)
        rw [orderAt_pow hU hz, ← hν, hq1, hνneg]
        exact_mod_cast (by linarith : (q : ℤ) * ν < -s - (q - 1) * -ν)
      rw [← hκ, orderAt_pow hU hz, ← hν] at this
      exact_mod_cast this
    have hqν : (q : ℤ) * ν ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hν0.le
    have hpqν : (p : ℤ) * ν - q * ν ≤ 0 := by nlinarith
    have hS : 0 ≤ ((p : ℤ) + m + n + 1) * s := by positivity
    rw [hρ', hκ', posPart_eq_zero.2 hqν, negPart_eq_neg.2 hpqν, hνneg]
    linarith

end Divisor

/-!
## The Integrated Bezout Estimate

For germs on `ℂ`, the pointwise estimate G2 integrates to an estimate for the proximity
functions, the divisor estimate B3 to one for the counting functions; together they give
`(p - q) T(r, a) + T(r, 1/Q(a)) ≤ T(r, P(a)/Q(a)) + (p + m + n + 3) · (Σ T(r, coefficients) + c)`.
-/

section Integration

variable {r : ℝ}

theorem characteristic_eq_proximity_add_logCounting (a : germRing ℂ univ) :
    characteristic a r
      = ValueDistribution.proximity (out a) ⊤ r + ValueDistribution.logCounting (out a) ⊤ r :=
  rfl

theorem characteristic_inv_eq_proximity_add_logCounting (a : germRing ℂ univ) (hr : r ≠ 0) :
    characteristic a⁻¹ r
      = ValueDistribution.proximity (out a) 0 r + ValueDistribution.logCounting (out a) 0 r := by
  rw [characteristic, ValueDistribution.characteristic_congr_codiscrete (out_inv a) hr,
    ← ValueDistribution.proximity_inv, ← ValueDistribution.logCounting_inv]
  rfl

/--
**The integrated Bezout estimate.** Let `P(a)`, `Q(a)` be monic polynomial expressions of
degrees `1 ≤ q ≤ p` in a nonzero germ `a`, both nonzero, with a Bezout certificate
`U(a) P(a) + V(a) Q(a) = 1` of degrees `m`, `n`. Then for `1 ≤ r`,
`(p - q) T(r, a) + T(r, 1/Q(a)) ≤ T(r, P(a)/Q(a)) + (p + m + n + 3) · (Σ T(r, coefficients) + c)`
with `c = log 2 + log p + log q + log (m + 1) + log (n + 1)`.
-/
theorem nsmul_characteristic_add_characteristic_inv_le_of_bezout {a : germRing ℂ univ}
    (ha : a ≠ 0) {c b u v : ℕ → germRing ℂ univ} {p q m n : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p)
    (hP : a ^ p + ∑ j ∈ range p, c j * a ^ j ≠ 0) (hQ : a ^ q + ∑ k ∈ range q, b k * a ^ k ≠ 0)
    (h : (∑ i ∈ range (m + 1), u i * a ^ i) * (a ^ p + ∑ j ∈ range p, c j * a ^ j)
      + (∑ i ∈ range (n + 1), v i * a ^ i) * (a ^ q + ∑ k ∈ range q, b k * a ^ k) = 1)
    (hr : 1 ≤ r) :
    ((p - q : ℕ) : ℝ) * characteristic a r
        + characteristic (a ^ q + ∑ k ∈ range q, b k * a ^ k)⁻¹ r
      ≤ characteristic ((a ^ p + ∑ j ∈ range p, c j * a ^ j)
          / (a ^ q + ∑ k ∈ range q, b k * a ^ k)) r
        + (p + m + n + 3) * (∑ j ∈ range p, characteristic (c j) r
          + ∑ k ∈ range q, characteristic (b k) r + ∑ i ∈ range (m + 1), characteristic (u i) r
          + ∑ i ∈ range (n + 1), characteristic (v i) r
          + (log 2 + log p + log q + log (m + 1) + log (n + 1))) := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  set P := a ^ p + ∑ j ∈ range p, c j * a ^ j with hP_def
  set Q := a ^ q + ∑ k ∈ range q, b k * a ^ k with hQ_def
  set Ua := ∑ i ∈ range (m + 1), u i * a ^ i with hUa_def
  set Va := ∑ i ∈ range (n + 1), v i * a ^ i with hVa_def
  set C : ℝ := log 2 + log p + log q + log (m + 1) + log (n + 1) with hC
  set K : ℝ := p + m + n + 3 with hK
  -- The representatives satisfy the polynomial identities away from a discrete set.
  have hBo : out Ua * out P + out Va * out Q =ᶠ[codiscrete ℂ] 1 := by
    have h₁ : out (Ua * P + Va * Q) =ᶠ[codiscreteWithin (univ : Set ℂ)]
        out Ua * out P + out Va * out Q :=
      (out_add _ _).trans ((out_mul _ _).add (out_mul _ _))
    rw [h] at h₁
    exact h₁.symm.trans out_one
  -- Integrability of all integrands.
  have hint : ∀ x : germRing ℂ univ, CircleIntegrable (fun z ↦ log⁺ ‖out x z‖) 0 r :=
    fun x ↦ (meromorphic_out x).meromorphicOn.circleIntegrable_posLog_norm
  have hintQ : CircleIntegrable (fun z ↦ log⁺ ‖(out Q)⁻¹ z‖) 0 r :=
    (meromorphic_out Q).inv.meromorphicOn.circleIntegrable_posLog_norm
  have hA : CircleIntegrable (((p - q : ℕ) : ℝ) • fun z ↦ log⁺ ‖out a z‖) 0 r :=
    IntervalIntegrable.const_mul (hint a) _
  have hc' : ∀ j ∈ range p, CircleIntegrable (fun z ↦ log⁺ ‖out (c j) z‖) 0 r := fun j _ ↦ hint _
  have hb' : ∀ k ∈ range q, CircleIntegrable (fun z ↦ log⁺ ‖out (b k) z‖) 0 r := fun k _ ↦ hint _
  have hu' : ∀ i ∈ range (m + 1), CircleIntegrable (fun z ↦ log⁺ ‖out (u i) z‖) 0 r :=
    fun i _ ↦ hint _
  have hv' : ∀ i ∈ range (n + 1), CircleIntegrable (fun z ↦ log⁺ ‖out (v i) z‖) 0 r :=
    fun i _ ↦ hint _
  have hSc := CircleIntegrable.sum (range p) hc'
  have hSb := CircleIntegrable.sum (range q) hb'
  have hSu := CircleIntegrable.sum (range (m + 1)) hu'
  have hSv := CircleIntegrable.sum (range (n + 1)) hv'
  have hCi : CircleIntegrable (fun _ : ℂ ↦ C) 0 r := circleIntegrable_const _ _ _
  have hS := (((hSc.add hSb).add hSu).add hSv).add hCi
  have hKS : CircleIntegrable (K • (∑ j ∈ range p, (fun z ↦ log⁺ ‖out (c j) z‖)
      + ∑ k ∈ range q, (fun z ↦ log⁺ ‖out (b k) z‖)
      + ∑ i ∈ range (m + 1), (fun z ↦ log⁺ ‖out (u i) z‖)
      + ∑ i ∈ range (n + 1), (fun z ↦ log⁺ ‖out (v i) z‖) + fun _ ↦ C)) 0 r :=
    IntervalIntegrable.const_mul hS _
  -- The proximity part: the pointwise estimate G2, integrated.
  have hm : ((p - q : ℕ) : ℝ) * ValueDistribution.proximity (out a) ⊤ r
      + ValueDistribution.proximity (out Q) 0 r
      ≤ ValueDistribution.proximity (out (P / Q)) ⊤ r
        + K * (∑ j ∈ range p, ValueDistribution.proximity (out (c j)) ⊤ r
          + ∑ k ∈ range q, ValueDistribution.proximity (out (b k)) ⊤ r
          + ∑ i ∈ range (m + 1), ValueDistribution.proximity (out (u i)) ⊤ r
          + ∑ i ∈ range (n + 1), ValueDistribution.proximity (out (v i)) ⊤ r + C) := by
    simp only [ValueDistribution.proximity_top, ValueDistribution.proximity_zero_of_complexValued]
    have key : circleAverage ((((p - q : ℕ) : ℝ) • fun z ↦ log⁺ ‖out a z‖)
        + fun z ↦ log⁺ ‖(out Q)⁻¹ z‖) 0 r
        ≤ circleAverage ((fun z ↦ log⁺ ‖out (P / Q) z‖)
          + K • (∑ j ∈ range p, (fun z ↦ log⁺ ‖out (c j) z‖)
            + ∑ k ∈ range q, (fun z ↦ log⁺ ‖out (b k) z‖)
            + ∑ i ∈ range (m + 1), (fun z ↦ log⁺ ‖out (u i) z‖)
            + ∑ i ∈ range (n + 1), (fun z ↦ log⁺ ‖out (v i) z‖) + fun _ ↦ C)) 0 r := by
      apply circleAverage_mono_codiscreteWithin hr0 (hA.add hintQ) ((hint _).add hKS)
      filter_upwards [(out_monic a c p).filter_mono (codiscreteWithin_mono (subset_univ _)),
        (out_monic a b q).filter_mono (codiscreteWithin_mono (subset_univ _)),
        (out_sum_mul_pow a u (range (m + 1))).filter_mono (codiscreteWithin_mono (subset_univ _)),
        (out_sum_mul_pow a v (range (n + 1))).filter_mono (codiscreteWithin_mono (subset_univ _)),
        (out_div P Q).filter_mono (codiscreteWithin_mono (subset_univ _)),
        hBo.filter_mono (codiscreteWithin_mono (subset_univ _))]
        with z hzP hzQ hzU hzV hzg hzB
      simp only [Pi.add_apply, Pi.smul_apply, Pi.inv_apply, Pi.mul_apply, Pi.pow_apply,
        Pi.div_apply, Pi.one_apply, Finset.sum_apply, smul_eq_mul,
        norm_inv] at hzP hzQ hzU hzV hzg hzB ⊢
      rw [hzg, hzP, hzQ, hK, hC]
      rw [hzU, hzP, hzV, hzQ] at hzB
      linarith [nsmul_posLog_norm_add_posLog_norm_inv_le_of_bezout hqp hzB]
    rwa [circleAverage_add hA hintQ, circleAverage_smul, circleAverage_add (hint _) hKS,
      circleAverage_smul, circleAverage_add (((hSc.add hSb).add hSu).add hSv) hCi,
      circleAverage_add ((hSc.add hSb).add hSu) hSv, circleAverage_add (hSc.add hSb) hSu,
      circleAverage_add hSc hSb, circleAverage_sum hc', circleAverage_sum hb',
      circleAverage_sum hu', circleAverage_sum hv', circleAverage_const, smul_eq_mul,
      smul_eq_mul] at key
  -- The counting part: the divisor estimate B3.
  have hN : ((p - q : ℕ) : ℝ) * ValueDistribution.logCounting (out a) ⊤ r
      + ValueDistribution.logCounting (out Q) 0 r
      ≤ ValueDistribution.logCounting (out (P / Q)) ⊤ r
        + ((p + m + n + 1 : ℕ) : ℝ) * (∑ j ∈ range p, ValueDistribution.logCounting (out (c j)) ⊤ r
          + ∑ k ∈ range q, ValueDistribution.logCounting (out (b k)) ⊤ r
          + ∑ i ∈ range (m + 1), ValueDistribution.logCounting (out (u i)) ⊤ r
          + ∑ i ∈ range (n + 1), ValueDistribution.logCounting (out (v i)) ⊤ r) := by
    have := locallyFinsuppWithin.logCounting_le
      (nsmul_negPart_divisor_add_posPart_divisor_le_of_bezout ha hq hqp hP hQ h) hr
    simp only [map_add, map_nsmul, map_sum, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
      GermRing.divisor] at this
    simp only [nsmul_eq_mul] at this
    simpa only [ValueDistribution.logCounting_top, ValueDistribution.logCounting_zero] using this
  -- The characteristics of the coefficients are the sums of their proximity and counting parts.
  have hTc : ∑ j ∈ range p, characteristic (c j) r
      = ∑ j ∈ range p, ValueDistribution.proximity (out (c j)) ⊤ r
        + ∑ j ∈ range p, ValueDistribution.logCounting (out (c j)) ⊤ r := by
    rw [← sum_add_distrib]; rfl
  have hTb : ∑ k ∈ range q, characteristic (b k) r
      = ∑ k ∈ range q, ValueDistribution.proximity (out (b k)) ⊤ r
        + ∑ k ∈ range q, ValueDistribution.logCounting (out (b k)) ⊤ r := by
    rw [← sum_add_distrib]; rfl
  have hTu : ∑ i ∈ range (m + 1), characteristic (u i) r
      = ∑ i ∈ range (m + 1), ValueDistribution.proximity (out (u i)) ⊤ r
        + ∑ i ∈ range (m + 1), ValueDistribution.logCounting (out (u i)) ⊤ r := by
    rw [← sum_add_distrib]; rfl
  have hTv : ∑ i ∈ range (n + 1), characteristic (v i) r
      = ∑ i ∈ range (n + 1), ValueDistribution.proximity (out (v i)) ⊤ r
        + ∑ i ∈ range (n + 1), ValueDistribution.logCounting (out (v i)) ⊤ r := by
    rw [← sum_add_distrib]; rfl
  have hN₀ : 0 ≤ ∑ j ∈ range p, ValueDistribution.logCounting (out (c j)) ⊤ r
      + ∑ k ∈ range q, ValueDistribution.logCounting (out (b k)) ⊤ r
      + ∑ i ∈ range (m + 1), ValueDistribution.logCounting (out (u i)) ⊤ r
      + ∑ i ∈ range (n + 1), ValueDistribution.logCounting (out (v i)) ⊤ r := by
    have := sum_nonneg fun j (_ : j ∈ range p) ↦
      ValueDistribution.logCounting_nonneg (f := out (c j)) (e := ⊤) hr
    have := sum_nonneg fun k (_ : k ∈ range q) ↦
      ValueDistribution.logCounting_nonneg (f := out (b k)) (e := ⊤) hr
    have := sum_nonneg fun i (_ : i ∈ range (m + 1)) ↦
      ValueDistribution.logCounting_nonneg (f := out (u i)) (e := ⊤) hr
    have := sum_nonneg fun i (_ : i ∈ range (n + 1)) ↦
      ValueDistribution.logCounting_nonneg (f := out (v i)) (e := ⊤) hr
    linarith
  have hK₂ : ((p + m + n + 1 : ℕ) : ℝ)
      * (∑ j ∈ range p, ValueDistribution.logCounting (out (c j)) ⊤ r
      + ∑ k ∈ range q, ValueDistribution.logCounting (out (b k)) ⊤ r
      + ∑ i ∈ range (m + 1), ValueDistribution.logCounting (out (u i)) ⊤ r
      + ∑ i ∈ range (n + 1), ValueDistribution.logCounting (out (v i)) ⊤ r)
      ≤ K * (∑ j ∈ range p, ValueDistribution.logCounting (out (c j)) ⊤ r
      + ∑ k ∈ range q, ValueDistribution.logCounting (out (b k)) ⊤ r
      + ∑ i ∈ range (m + 1), ValueDistribution.logCounting (out (u i)) ⊤ r
      + ∑ i ∈ range (n + 1), ValueDistribution.logCounting (out (v i)) ⊤ r) :=
    mul_le_mul_of_nonneg_right (by rw [hK]; push_cast; linarith) hN₀
  rw [hTc, hTb, hTu, hTv, characteristic_inv_eq_proximity_add_logCounting Q hr0,
    characteristic_eq_proximity_add_logCounting a, characteristic_eq_proximity_add_logCounting]
  linarith

end Integration

/-!
## Polynomials over a Growth Field, Evaluated at a Germ
-/

section Polynomials

variable {l : Filter ℝ} {G : (ℝ → ℝ) → Prop}

/-- `aeval a P`, as a sum over the coefficients of `P`, coerced to the field of germs. -/
theorem aeval_eq_sum_range_coe (hG : IsGrowthClass l G) (a : germRing ℂ univ)
    (P : (growthField hG)[X]) :
    aeval a P = ∑ j ∈ range (P.natDegree + 1), (P.coeff j : germRing ℂ univ) * a ^ j := by
  rw [aeval_eq_sum_range]
  simp only [Algebra.smul_def, IntermediateField.algebraMap_apply]

/-- `aeval a P` for monic `P`, in monic normal form. -/
theorem aeval_eq_monic (hG : IsGrowthClass l G) (a : germRing ℂ univ) {P : (growthField hG)[X]}
    (hP : P.Monic) :
    aeval a P
      = a ^ P.natDegree + ∑ j ∈ range P.natDegree, (P.coeff j : germRing ℂ univ) * a ^ j := by
  have := congrArg (aeval a) hP.as_sum
  simpa using this

/-- If `a` lies in the growth field, so does every polynomial expression in `a` with
coefficients in the growth field. -/
theorem aeval_mem_growthField (hG : IsGrowthClass l G) {a : germRing ℂ univ}
    (ha : a ∈ growthField hG) (P : (growthField hG)[X]) : aeval a P ∈ growthField hG := by
  have : a = algebraMap (growthField hG) (germRing ℂ univ) ⟨a, ha⟩ := rfl
  rw [this, aeval_algebraMap_apply_eq_algebraMap_eval]
  exact SetLike.coe_mem _

/-- If `a` does not lie in the growth field, no nonzero polynomial with coefficients in the
growth field vanishes at `a` (relative algebraic closedness, T6). -/
theorem aeval_ne_zero_of_notMem_growthField (hG : IsGrowthClass l G) {a : germRing ℂ univ}
    (ha : a ∉ growthField hG) {P : (growthField hG)[X]} (hP : P ≠ 0) : aeval a P ≠ 0 :=
  fun h ↦ ha (mem_growthField_of_isAlgebraic hG ⟨P, hP, h⟩)

end Polynomials

/-!
## The Upper Bound (G1)
-/

section UpperBound

variable {l : Filter ℝ} {G : (ℝ → ℝ) → Prop}

/-- G1, auxiliary form: the upper bound of the rational Valiron–Mohon'ko identity, by strong
induction on the degree of the denominator along the Euclidean algorithm. The error term is
eventually nonnegative. -/
theorem characteristic_aeval_div_le_aux (hG : IsGrowthClass l G) (a : germRing ℂ univ) (q : ℕ) :
    ∀ P Q : (growthField hG)[X], Q ≠ 0 → Q.natDegree = q →
      ∃ u, G u ∧ ∀ᶠ r in l, 0 ≤ u r ∧
        characteristic (aeval a P / aeval a Q) r
          ≤ max P.natDegree Q.natDegree * characteristic a r + u r := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro P Q hQ hq
  -- If `Q(a) = 0`, the quotient is `0`.
  by_cases hQa : aeval a Q = 0
  · refine ⟨fun _ ↦ 0, hG.const 0, ?_⟩
    filter_upwards [hG.le_atTop (eventually_ge_atTop 1)] with r hr
    rw [hQa, div_zero, characteristic_zero (zero_lt_one.trans_le hr).ne']
    have := characteristic_nonneg a hr
    exact ⟨le_rfl, by positivity⟩
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · -- `Q` is a nonzero constant `c`: `T(P(a)/c) ≤ T(P(a)) + T(c⁻¹)`.
    obtain ⟨c, rfl⟩ := natDegree_eq_zero.1 hq
    rw [aeval_C, natDegree_C, max_eq_left (Nat.zero_le _)]
    have hc : G (characteristic (algebraMap (growthField hG) (germRing ℂ univ) c)⁻¹) := by
      have := (c⁻¹).2
      rwa [IntermediateField.coe_inv] at this
    refine ⟨(∑ j ∈ range (P.natDegree + 1), characteristic (P.coeff j : germRing ℂ univ))
      + (fun _ ↦ log (P.natDegree + 1))
      + characteristic (algebraMap (growthField hG) (germRing ℂ univ) c)⁻¹,
      hG.add (hG.add (hG.sum fun j _ ↦ (P.coeff j).2) (hG.const _)) hc, ?_⟩
    filter_upwards [hG.le_atTop (eventually_ge_atTop 1)] with r hr
    simp only [Pi.add_apply, Finset.sum_apply]
    have h₁ := characteristic_aeval_le hG a P hr
    have h₂ := characteristic_mul_le (aeval a P)
      (algebraMap (growthField hG) (germRing ℂ univ) c)⁻¹ hr
    have h₃ := characteristic_nonneg (algebraMap (growthField hG) (germRing ℂ univ) c)⁻¹ hr
    have h₄ : 0 ≤ ∑ j ∈ range (P.natDegree + 1), characteristic (P.coeff j : germRing ℂ univ) r :=
      sum_nonneg fun j _ ↦ characteristic_nonneg _ hr
    have h₅ : 0 ≤ log ((P.natDegree : ℝ) + 1) :=
      log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) P.natDegree])
    rw [div_eq_mul_inv]
    exact ⟨by linarith, by linarith⟩
  rcases le_or_gt q P.natDegree with hpq | hpq
  · -- `deg Q ≤ deg P`: Euclidean division `P = Q * S + P₁` with `deg P₁ < deg Q`.
    set S := P / Q with hS_def
    set P₁ := P % Q with hP₁_def
    have hdiv : Q * S + P₁ = P := EuclideanDomain.div_add_mod P Q
    have hP₁ : P₁.natDegree < q := by
      rcases eq_or_ne P₁ 0 with h0 | h0
      · rw [h0, natDegree_zero]; exact hq0
      · exact hq ▸ natDegree_lt_natDegree h0 (degree_mod_lt P hQ)
    have hS : S.natDegree = P.natDegree - q := by
      rw [hS_def, Polynomial.div_def, natDegree_C_mul (inv_ne_zero (leadingCoeff_ne_zero.2 hQ)),
        natDegree_divByMonic _ (monic_mul_leadingCoeff_inv hQ),
        natDegree_mul_leadingCoeff_inv _ hQ, hq]
    have hg : aeval a P / aeval a Q = aeval a S + aeval a P₁ / aeval a Q := by
      calc aeval a P / aeval a Q = (aeval a Q * aeval a S + aeval a P₁) / aeval a Q := by
            rw [← map_mul, ← map_add, hdiv]
        _ = _ := by rw [add_div, mul_div_cancel_left₀ _ hQa]
    -- The remainder term: `T(P₁(a)/Q(a)) ≤ q T(a) + u₂` by the induction hypothesis.
    have hrem : ∃ u₂, G u₂ ∧ ∀ᶠ r in l, 0 ≤ u₂ r ∧
        characteristic (aeval a P₁ / aeval a Q) r ≤ q * characteristic a r + u₂ r := by
      rcases eq_or_ne P₁ 0 with h0 | h0
      · refine ⟨fun _ ↦ 0, hG.const 0, ?_⟩
        filter_upwards [hG.le_atTop (eventually_ge_atTop 1)] with r hr
        rw [h0, map_zero, zero_div, characteristic_zero (zero_lt_one.trans_le hr).ne']
        have := characteristic_nonneg a hr
        exact ⟨le_rfl, by positivity⟩
      · obtain ⟨u₂, hu₂, h₂⟩ := ih P₁.natDegree hP₁ Q P₁ h0 rfl
        obtain ⟨c₀, hc₀⟩ := exists_abs_characteristic_inv_sub_le (aeval a P₁ / aeval a Q)
        refine ⟨u₂ + fun _ ↦ c₀, hG.add hu₂ (hG.const _), ?_⟩
        filter_upwards [h₂] with r ⟨hr₀, hr⟩
        have hc₀' := abs_le.1 (hc₀ r)
        rw [inv_div] at hc₀'
        rw [hq, max_eq_left hP₁.le] at hr
        simp only [Pi.add_apply]
        exact ⟨by linarith [(abs_nonneg _).trans (hc₀ r)], by linarith⟩
    obtain ⟨u₂, hu₂, h₂⟩ := hrem
    refine ⟨(∑ j ∈ range (S.natDegree + 1), characteristic (S.coeff j : germRing ℂ univ))
      + (fun _ ↦ log (S.natDegree + 1)) + u₂ + (fun _ ↦ log 2),
      hG.add (hG.add (hG.add (hG.sum fun j _ ↦ (S.coeff j).2) (hG.const _)) hu₂) (hG.const _),
      ?_⟩
    filter_upwards [h₂, hG.le_atTop (eventually_ge_atTop 1)] with r ⟨hu₂r, hr₂⟩ hr
    simp only [Pi.add_apply, Finset.sum_apply]
    have h₁ := characteristic_aeval_le hG a S hr
    have h₃ := characteristic_add_le (aeval a S) (aeval a P₁ / aeval a Q) hr
    have h₄ : 0 ≤ ∑ j ∈ range (S.natDegree + 1), characteristic (S.coeff j : germRing ℂ univ) r :=
      sum_nonneg fun j _ ↦ characteristic_nonneg _ hr
    have h₅ : 0 ≤ log ((S.natDegree : ℝ) + 1) :=
      log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) S.natDegree])
    have h₆ : 0 ≤ log (2 : ℝ) := log_nonneg one_le_two
    have h₇ : ((S.natDegree : ℕ) : ℝ) * characteristic a r
        = (P.natDegree - q) * characteristic a r := by
      rw [hS, Nat.cast_sub hpq]
    rw [hg, hq, max_eq_left hpq]
    exact ⟨by linarith, by linarith⟩
  · -- `deg P < deg Q`: invert, `T(P(a)/Q(a)) = T(Q(a)/P(a)) + O(1)`.
    rcases eq_or_ne P 0 with rfl | hP
    · refine ⟨fun _ ↦ 0, hG.const 0, ?_⟩
      filter_upwards [hG.le_atTop (eventually_ge_atTop 1)] with r hr
      rw [map_zero, zero_div, characteristic_zero (zero_lt_one.trans_le hr).ne']
      have := characteristic_nonneg a hr
      exact ⟨le_rfl, by positivity⟩
    · obtain ⟨u₂, hu₂, h₂⟩ := ih P.natDegree (hq ▸ hpq) Q P hP rfl
      obtain ⟨c₀, hc₀⟩ := exists_abs_characteristic_inv_sub_le (aeval a P / aeval a Q)
      refine ⟨u₂ + fun _ ↦ c₀, hG.add hu₂ (hG.const _), ?_⟩
      filter_upwards [h₂] with r ⟨hr₀, hr⟩
      have hc₀' := abs_le.1 (hc₀ r)
      rw [inv_div] at hc₀'
      rw [max_comm]
      simp only [Pi.add_apply]
      exact ⟨by linarith [(abs_nonneg _).trans (hc₀ r)], by linarith⟩

/-- **The upper bound of the rational Valiron–Mohon'ko identity** (G1): for polynomials
`P, Q` with coefficients in the growth field of `G`, `Q ≠ 0`,
`T(r, P(a)/Q(a)) ≤ max (deg P) (deg Q) · T(r, a) + u(r)` with `u ∈ G`. No coprimality is
needed. -/
theorem characteristic_aeval_div_le (hG : IsGrowthClass l G) (a : germRing ℂ univ)
    (P : (growthField hG)[X]) {Q : (growthField hG)[X]} (hQ : Q ≠ 0) :
    ∃ u, G u ∧ ∀ᶠ r in l,
      characteristic (aeval a P / aeval a Q) r
        ≤ max P.natDegree Q.natDegree * characteristic a r + u r := by
  obtain ⟨u, hu, h⟩ := characteristic_aeval_div_le_aux hG a Q.natDegree P Q hQ rfl
  exact ⟨u, hu, h.mono fun r hr ↦ hr.2⟩

end UpperBound

/-!
## The Lower Bound (G3)
-/

section LowerBound

variable {l : Filter ℝ} {G : (ℝ → ℝ) → Prop}

/-- G3 for monic `P, Q` with `1 ≤ deg Q ≤ deg P`: the integrated Bezout estimate, combined with
the First Main Theorem for `Q(a)` and the polynomial identity F5. -/
theorem nsmul_characteristic_le_characteristic_aeval_div_of_monic (hG : IsGrowthClass l G)
    (a : germRing ℂ univ) {P Q : (growthField hG)[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hPQ : IsCoprime P Q) (hq : 1 ≤ Q.natDegree) (hqp : Q.natDegree ≤ P.natDegree) :
    ∃ u, G u ∧ ∀ᶠ r in l, 0 ≤ u r ∧
      P.natDegree * characteristic a r ≤ characteristic (aeval a P / aeval a Q) r + u r := by
  by_cases ha : a ∈ growthField hG
  · -- `a` is small: both sides are small.
    refine ⟨P.natDegree • characteristic a, hG.nsmul ha _, ?_⟩
    filter_upwards [hG.le_atTop (eventually_ge_atTop 1)] with r hr
    rw [Pi.smul_apply, nsmul_eq_mul]
    have := characteristic_nonneg (aeval a P / aeval a Q) hr
    have := characteristic_nonneg a hr
    exact ⟨by positivity, by linarith⟩
  -- `a` is not small: `a`, `P(a)`, `Q(a)` are nonzero.
  have ha0 : a ≠ 0 := fun h ↦ ha (h ▸ zero_mem _)
  have hPa := aeval_ne_zero_of_notMem_growthField hG ha hP.ne_zero
  have hQa := aeval_ne_zero_of_notMem_growthField hG ha hQ.ne_zero
  -- The Bezout certificate, evaluated at `a`.
  obtain ⟨U, V, hUV⟩ := hPQ
  have hB := congrArg (aeval a) hUV
  rw [map_add, map_mul, map_mul, map_one, aeval_eq_sum_range_coe hG a U,
    aeval_eq_sum_range_coe hG a V, aeval_eq_monic hG a hP, aeval_eq_monic hG a hQ] at hB
  rw [aeval_eq_monic hG a hP] at hPa
  rw [aeval_eq_monic hG a hQ] at hQa
  -- The integrated Bezout estimate.
  have hest := fun r (hr : 1 ≤ r) ↦
    nsmul_characteristic_add_characteristic_inv_le_of_bezout ha0 hq hqp hPa hQa hB hr
  simp only [← aeval_eq_monic hG a hP, ← aeval_eq_monic hG a hQ] at hest
  -- The First Main Theorem for `Q(a)` and the polynomial identity for `Q`.
  obtain ⟨c₀, hc₀⟩ := exists_abs_characteristic_inv_sub_le (aeval a Q)
  obtain ⟨u₀, hu₀, h₀⟩ := exists_abs_characteristic_aeval_sub_le hG a hQ.ne_zero
  set C : ℝ := log 2 + log P.natDegree + log Q.natDegree + log (U.natDegree + 1)
    + log (V.natDegree + 1) with hC
  have hC₀ : 0 ≤ C := by
    have := log_natCast_nonneg P.natDegree
    have := log_natCast_nonneg Q.natDegree
    have : 0 ≤ log ((U.natDegree : ℝ) + 1) :=
      log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) U.natDegree])
    have : 0 ≤ log ((V.natDegree : ℝ) + 1) :=
      log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) V.natDegree])
    have := log_nonneg (one_le_two (α := ℝ))
    rw [hC]
    linarith
  refine ⟨(P.natDegree + U.natDegree + V.natDegree + 3)
      • (∑ j ∈ range P.natDegree, characteristic (P.coeff j : germRing ℂ univ)
        + ∑ k ∈ range Q.natDegree, characteristic (Q.coeff k : germRing ℂ univ)
        + ∑ i ∈ range (U.natDegree + 1), characteristic (U.coeff i : germRing ℂ univ)
        + ∑ i ∈ range (V.natDegree + 1), characteristic (V.coeff i : germRing ℂ univ)
        + fun _ ↦ C) + u₀ + fun _ ↦ c₀,
    hG.add (hG.add (hG.nsmul (hG.add (hG.add (hG.add (hG.add (hG.sum fun j _ ↦ (P.coeff j).2)
      (hG.sum fun k _ ↦ (Q.coeff k).2)) (hG.sum fun i _ ↦ (U.coeff i).2))
      (hG.sum fun i _ ↦ (V.coeff i).2)) (hG.const _)) _) hu₀) (hG.const _), ?_⟩
  filter_upwards [h₀, hG.le_atTop (eventually_ge_atTop 1)] with r hr₀ hr
  have h₁ := hest r hr
  have h₂ := abs_le.1 (hc₀ r)
  have h₃ := abs_le.1 hr₀
  have hc₀' : 0 ≤ c₀ := (abs_nonneg _).trans (hc₀ r)
  have hu₀' : 0 ≤ u₀ r := (abs_nonneg _).trans hr₀
  have hpq : ((P.natDegree - Q.natDegree : ℕ) : ℝ) = P.natDegree - Q.natDegree :=
    Nat.cast_sub hqp
  rw [hpq] at h₁
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
  simp only [nsmul_eq_mul]
  have hT₀ : 0 ≤ ∑ j ∈ range P.natDegree, characteristic (P.coeff j : germRing ℂ univ) r
      + ∑ k ∈ range Q.natDegree, characteristic (Q.coeff k : germRing ℂ univ) r
      + ∑ i ∈ range (U.natDegree + 1), characteristic (U.coeff i : germRing ℂ univ) r
      + ∑ i ∈ range (V.natDegree + 1), characteristic (V.coeff i : germRing ℂ univ) r + C := by
    have := sum_nonneg fun j (_ : j ∈ range P.natDegree) ↦ characteristic_nonneg (P.coeff j :
      germRing ℂ univ) hr
    have := sum_nonneg fun k (_ : k ∈ range Q.natDegree) ↦ characteristic_nonneg (Q.coeff k :
      germRing ℂ univ) hr
    have := sum_nonneg fun i (_ : i ∈ range (U.natDegree + 1)) ↦ characteristic_nonneg
      (U.coeff i : germRing ℂ univ) hr
    have := sum_nonneg fun i (_ : i ∈ range (V.natDegree + 1)) ↦ characteristic_nonneg
      (V.coeff i : germRing ℂ univ) hr
    linarith
  have hK : 0 ≤ ((P.natDegree + U.natDegree + V.natDegree + 3 : ℕ) : ℝ) * (∑ j ∈ range P.natDegree,
      characteristic (P.coeff j : germRing ℂ univ) r
      + ∑ k ∈ range Q.natDegree, characteristic (Q.coeff k : germRing ℂ univ) r
      + ∑ i ∈ range (U.natDegree + 1), characteristic (U.coeff i : germRing ℂ univ) r
      + ∑ i ∈ range (V.natDegree + 1), characteristic (V.coeff i : germRing ℂ univ) r + C) :=
    mul_nonneg (Nat.cast_nonneg _) hT₀
  push_cast at hK h₁ ⊢
  exact ⟨by linarith, by linarith⟩

/-- G3 for `deg Q ≤ deg P`: reduction to the monic case. -/
theorem nsmul_characteristic_le_characteristic_aeval_div_of_le (hG : IsGrowthClass l G)
    (a : germRing ℂ univ) {P Q : (growthField hG)[X]} (hPQ : IsCoprime P Q) (hQ : Q ≠ 0)
    (hqp : Q.natDegree ≤ P.natDegree) :
    ∃ u, G u ∧ ∀ᶠ r in l, 0 ≤ u r ∧
      P.natDegree * characteristic a r ≤ characteristic (aeval a P / aeval a Q) r + u r := by
  rcases Nat.eq_zero_or_pos Q.natDegree with hq0 | hq0
  · -- `Q` is a nonzero constant `c`: `T(P(a)) ≤ T(P(a)/c) + T(c)`.
    obtain ⟨c, rfl⟩ := natDegree_eq_zero.1 hq0
    have hc : c ≠ 0 := by rintro rfl; simp at hQ
    rcases eq_or_ne P 0 with rfl | hP0
    · refine ⟨fun _ ↦ 0, hG.const 0, ?_⟩
      filter_upwards [hG.le_atTop (eventually_ge_atTop 1)] with r hr
      have := characteristic_nonneg (aeval a (0 : (growthField hG)[X]) / aeval a (C c)) hr
      simp only [natDegree_zero, Nat.cast_zero, zero_mul]
      exact ⟨le_rfl, by linarith⟩
    · obtain ⟨u₀, hu₀, h₀⟩ := exists_abs_characteristic_aeval_sub_le hG a hP0
      refine ⟨u₀ + characteristic (algebraMap (growthField hG) (germRing ℂ univ) c),
        hG.add hu₀ c.2, ?_⟩
      filter_upwards [h₀, hG.le_atTop (eventually_ge_atTop 1)] with r hr₀ hr
      have hc' : algebraMap (growthField hG) (germRing ℂ univ) c ≠ 0 :=
        fun h ↦ hc (ZeroMemClass.coe_eq_zero.1 h)
      have h₁ : aeval a P = aeval a P / aeval a (C c)
          * algebraMap (growthField hG) (germRing ℂ univ) c := by
        rw [aeval_C, div_mul_cancel₀ _ hc']
      have h₂ := characteristic_mul_le (aeval a P / aeval a (C c))
        (algebraMap (growthField hG) (germRing ℂ univ) c) hr
      rw [← h₁] at h₂
      have h₃ := abs_le.1 hr₀
      have hu₀' : 0 ≤ u₀ r := (abs_nonneg _).trans hr₀
      have h₄ := characteristic_nonneg (algebraMap (growthField hG) (germRing ℂ univ) c) hr
      simp only [Pi.add_apply]
      exact ⟨by linarith, by linarith⟩
  · -- Normalize `P` and `Q` to be monic.
    have hP0 : P ≠ 0 := by
      rintro rfl
      rw [natDegree_zero] at hqp
      omega
    set P' := P * C (leadingCoeff P)⁻¹ with hP'_def
    set Q' := Q * C (leadingCoeff Q)⁻¹ with hQ'_def
    have hP' : P'.Monic := monic_mul_leadingCoeff_inv hP0
    have hQ' : Q'.Monic := monic_mul_leadingCoeff_inv hQ
    have hdP : P'.natDegree = P.natDegree := natDegree_mul_leadingCoeff_inv P hP0
    have hdQ : Q'.natDegree = Q.natDegree := natDegree_mul_leadingCoeff_inv Q hQ
    have hPQ' : IsCoprime P' Q' :=
      (isCoprime_mul_units_right
        (isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hP0))))
        (isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hQ)))) P Q).2 hPQ
    obtain ⟨u₀, hu₀, h₀⟩ := nsmul_characteristic_le_characteristic_aeval_div_of_monic hG a hP' hQ'
      hPQ' (hdQ ▸ hq0) (by rw [hdP, hdQ]; exact hqp)
    -- `P'(a)/Q'(a) = P(a)/Q(a) · d` with the small constant `d = (lc P)⁻¹ lc Q`.
    set d : growthField hG := (leadingCoeff P)⁻¹ * leadingCoeff Q with hd_def
    have hg : aeval a P' / aeval a Q'
        = aeval a P / aeval a Q * algebraMap (growthField hG) (germRing ℂ univ) d := by
      simp only [hP'_def, hQ'_def, hd_def, map_mul, aeval_C, map_inv₀]
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
      ring
    refine ⟨u₀ + characteristic (algebraMap (growthField hG) (germRing ℂ univ) d),
      hG.add hu₀ d.2, ?_⟩
    filter_upwards [h₀, hG.le_atTop (eventually_ge_atTop 1)] with r ⟨hr₀, hr₁⟩ hr
    rw [hdP, hg] at hr₁
    have h₁ := characteristic_mul_le (aeval a P / aeval a Q)
      (algebraMap (growthField hG) (germRing ℂ univ) d) hr
    have h₂ := characteristic_nonneg (algebraMap (growthField hG) (germRing ℂ univ) d) hr
    simp only [Pi.add_apply]
    exact ⟨by linarith, by linarith⟩

/-- **The lower bound of the rational Valiron–Mohon'ko identity** (G3): for coprime polynomials
`P, Q` with coefficients in the growth field of `G`, `Q ≠ 0`,
`max (deg P) (deg Q) · T(r, a) ≤ T(r, P(a)/Q(a)) + u(r)` with `u ∈ G`. -/
theorem nsmul_characteristic_le_characteristic_aeval_div (hG : IsGrowthClass l G)
    (a : germRing ℂ univ) {P Q : (growthField hG)[X]} (hPQ : IsCoprime P Q) (hQ : Q ≠ 0) :
    ∃ u, G u ∧ ∀ᶠ r in l, 0 ≤ u r ∧
      max P.natDegree Q.natDegree * characteristic a r
        ≤ characteristic (aeval a P / aeval a Q) r + u r := by
  rcases le_or_gt Q.natDegree P.natDegree with hqp | hpq
  · rw [max_eq_left hqp]
    exact nsmul_characteristic_le_characteristic_aeval_div_of_le hG a hPQ hQ hqp
  · rw [max_eq_right hpq.le]
    have hP : P ≠ 0 := by
      rintro rfl
      have := natDegree_eq_zero_of_isUnit (isCoprime_zero_left.1 hPQ)
      rw [natDegree_zero] at hpq
      omega
    obtain ⟨u₀, hu₀, h₀⟩ :=
      nsmul_characteristic_le_characteristic_aeval_div_of_le hG a hPQ.symm hP hpq.le
    obtain ⟨c₀, hc₀⟩ := exists_abs_characteristic_inv_sub_le (aeval a P / aeval a Q)
    refine ⟨u₀ + fun _ ↦ c₀, hG.add hu₀ (hG.const _), ?_⟩
    filter_upwards [h₀] with r ⟨hr₀, hr⟩
    have hc₀' := abs_le.1 (hc₀ r)
    rw [inv_div] at hc₀'
    simp only [Pi.add_apply]
    exact ⟨by linarith [(abs_nonneg _).trans (hc₀ r)], by linarith⟩

end LowerBound

/-!
## The Valiron–Mohon'ko Identity for Rational Functions
-/

section Main

variable {l : Filter ℝ} {G : (ℝ → ℝ) → Prop}

/-- **The Valiron–Mohon'ko identity for rational functions** (T8): for coprime polynomials
`P, Q` with coefficients in the growth field of `G`, `Q ≠ 0`, and any meromorphic germ `a`,
`T(r, P(a)/Q(a)) = max (deg P) (deg Q) · T(r, a) + u(r)` with `u ∈ G`. -/
theorem exists_abs_characteristic_aeval_div_sub_le (hG : IsGrowthClass l G)
    (a : germRing ℂ univ) {P Q : (growthField hG)[X]} (hPQ : IsCoprime P Q) (hQ : Q ≠ 0) :
    ∃ u, G u ∧ ∀ᶠ r in l,
      |characteristic (aeval a P / aeval a Q) r
        - max P.natDegree Q.natDegree * characteristic a r| ≤ u r := by
  obtain ⟨u₁, hu₁, h₁⟩ := characteristic_aeval_div_le_aux hG a Q.natDegree P Q hQ rfl
  obtain ⟨u₂, hu₂, h₂⟩ := nsmul_characteristic_le_characteristic_aeval_div hG a hPQ hQ
  refine ⟨u₁ + u₂, hG.add hu₁ hu₂, ?_⟩
  filter_upwards [h₁, h₂] with r ⟨hu₁r, hr₁⟩ ⟨hu₂r, hr₂⟩
  rw [Pi.add_apply]
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Laine, Theorem 2.2.5** (T9): if `f` is a meromorphic germ whose characteristic tends to
infinity along `l ≤ atTop`, and `R = P/Q` is a rational function with coprime numerator and
denominator in the field `S(f)` of small functions with respect to `f`, then
`T(r, R(f)) = deg R · T(r, f) + o(T(r, f))` along `l`. The classical choice is
`l = volume.cofinite ⊓ atTop`. -/
theorem characteristic_aeval_div_sub_isLittleO (hl : l ≤ atTop) {f : germRing ℂ univ}
    (hf : Tendsto (characteristic f) l atTop) {P Q : (smallFunctions hl hf)[X]}
    (hPQ : IsCoprime P Q) (hQ : Q ≠ 0) :
    (fun r ↦ characteristic (aeval f P / aeval f Q) r
      - max P.natDegree Q.natDegree * characteristic f r) =o[l] characteristic f := by
  obtain ⟨u, hu, h⟩ := exists_abs_characteristic_aeval_div_sub_le (isGrowthClass_isLittleO hl hf)
    f hPQ hQ
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 ?_) hu
  filter_upwards [h] with r hr
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact hr.trans (le_abs_self _)

end Main

end MeromorphicOn.GermRing
