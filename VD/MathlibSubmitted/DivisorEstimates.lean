/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Divisor Estimates for Polynomial Relations — Algebraic Dependence work package B

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §4.

Mathlib targets (one PR, no new file; submitted as PR #44629):
- order-level lemmas: `Mathlib/Analysis/Meromorphic/Order.lean` (B1),
- divisor-level results: `Mathlib/Analysis/Meromorphic/Divisor.lean` (B2).

Dependencies: none within the project. The proofs below are kept verbatim in sync with the PR;
the section variables mirror those of the two target files.

## Main results

- B1, `le_meromorphicOrderAt_sum`: the order of a finite sum is at least the minimum of the
  orders of the summands.
- `exists_meromorphicOrderAt_le_of_monic_lt`: the order-level heart of B2. If `f` has order
  `n` at `x` and the monic expression `f ^ d + Σ_{j<d} a j * f ^ j` has order greater than
  `d * n`, then the leading term `f ^ d` must be cancelled by some `a j * f ^ j`, so some
  coefficient `a j` has order at most `(d - j) * n`.
- B2, `MeromorphicOn.nsmul_negPart_divisor_le_of_monic_eq`: the **pole divisor under a monic
  relation**, `d • (div f)⁻ ≤ (div (f ^ d + Σ_{j<d} a j * f ^ j))⁻ + d • Σ_{j<d} (div (a j))⁻`.
- `MeromorphicOn.negPart_divisor_sum_mul_pow_le` (for package D): the **pole divisor of a
  polynomial expression**, `(div (Σ_{j≤d} a j * f ^ j))⁻ ≤ Σ_{j≤d} (div (a j))⁻ + d • (div f)⁻`.

The divisor estimate B3 for quotients with a Bezout certificate (plan §4, needed for the
rational Valiron–Mohon'ko identity) will be added together with package G.
-/

@[expose] public section

open Filter Set Topology

/-!
## Order of a Finite Sum
-/

section OrderLevel

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {x : 𝕜}

/--
The order of a finite sum is at least the minimum of the orders of the summands: if every summand
has order at least `n`, so does the sum. Finite-sum version of `meromorphicOrderAt_add`.
-/
theorem le_meromorphicOrderAt_sum {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E} {n : WithTop ℤ}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x) (hn : ∀ i ∈ s, n ≤ meromorphicOrderAt (f i) x) :
    n ≤ meromorphicOrderAt (∑ i ∈ s, f i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, meromorphicOrderAt_eq_top_iff.2 (by simp)]
    exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hf' : ∀ i ∈ s, MeromorphicAt (f i) x := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hn' : ∀ i ∈ s, n ≤ meromorphicOrderAt (f i) x :=
      fun i hi ↦ hn i (Finset.mem_insert_of_mem hi)
    exact (le_min (hn a (Finset.mem_insert_self a s)) (ih hf' hn')).trans
      (meromorphicOrderAt_add (hf a (Finset.mem_insert_self a s)) (MeromorphicAt.sum hf'))

/-- In `WithTop ℤ`, a strict lower bound by an integer improves to `+ 1`. -/
private lemma coe_add_one_le_of_coe_lt {m : ℤ} {y : WithTop ℤ} (h : (m : WithTop ℤ) < y) :
    ((m + 1 : ℤ) : WithTop ℤ) ≤ y :=
  WithTop.coe_le_iff.2 fun c hc ↦ Int.add_one_le_iff.2 (WithTop.coe_lt_iff.1 h c hc)

/--
If `f` has order `n` at `x` and the monic expression `f ^ d + Σ_{j<d} a j * f ^ j` has order greater
than `d * n`, then the leading term `f ^ d` is cancelled by one of the other terms: some coefficient
`a j` has order at most `(d - j) * n`.
-/
theorem exists_meromorphicOrderAt_le_of_monic_lt {f : 𝕜 → 𝕜'} {a : ℕ → 𝕜 → 𝕜'} {d : ℕ} {n : ℤ}
    (hf : MeromorphicAt f x) (ha : ∀ j, MeromorphicAt (a j) x) (hn : meromorphicOrderAt f x = n)
    (hh : ((d * n : ℤ) : WithTop ℤ) <
      meromorphicOrderAt (f ^ d + ∑ j ∈ Finset.range d, a j * f ^ j) x) :
    ∃ j ∈ Finset.range d, meromorphicOrderAt (a j) x ≤ (((d : ℤ) - j) * n : ℤ) := by
  by_contra! hcon
  have hterms : ∀ j ∈ Finset.range d, MeromorphicAt (a j * f ^ j) x :=
    fun j _ ↦ (ha j).mul (hf.pow j)
  -- Every term `a j * f ^ j` has order at least `d * n + 1`.
  have hterm : ∀ j ∈ Finset.range d,
      ((d * n + 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (a j * f ^ j) x := by
    intro j hj
    rw [meromorphicOrderAt_mul (ha j) (hf.pow j), meromorphicOrderAt_pow hf, hn]
    calc ((d * n + 1 : ℤ) : WithTop ℤ)
        = (((d : ℤ) - j) * n + 1 : ℤ) + ((j * n : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]; congr 1; ring
      _ ≤ meromorphicOrderAt (a j) x + ((j * n : ℤ) : WithTop ℤ) := by
          gcongr
          exact coe_add_one_le_of_coe_lt (hcon j hj)
      _ = meromorphicOrderAt (a j) x + (j : WithTop ℤ) * (n : WithTop ℤ) := by
          rw [WithTop.coe_mul, WithTop.coe_natCast]
  -- Hence so does the sum, and therefore `f ^ d = (f ^ d + Σ) - Σ`.
  have hsum : ((d * n + 1 : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (∑ j ∈ Finset.range d, a j * f ^ j) x :=
    le_meromorphicOrderAt_sum hterms hterm
  have key : ((d * n + 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (f ^ d) x := by
    rw [show f ^ d = (f ^ d + ∑ j ∈ Finset.range d, a j * f ^ j)
        + -(∑ j ∈ Finset.range d, a j * f ^ j) from (add_neg_cancel_right _ _).symm]
    refine (le_min (coe_add_one_le_of_coe_lt hh) ?_).trans
      (meromorphicOrderAt_add ((hf.pow d).add (MeromorphicAt.sum hterms))
        (MeromorphicAt.sum hterms).neg)
    rwa [← meromorphicOrderAt_neg]
  -- But `f ^ d` has order exactly `d * n`.
  rw [meromorphicOrderAt_pow hf, hn, ← WithTop.coe_natCast (α := ℤ), ← WithTop.coe_mul,
    WithTop.coe_le_coe] at key
  omega

end OrderLevel

namespace MeromorphicOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜}

/-!
## Pole Divisors of Polynomial Expressions
-/

open Finset in
/--
**Pole divisor under a monic relation**: `d` times the pole divisor of `f` is bounded by the pole
divisor of `f ^ d + Σ_{j<d} a j * f ^ j` plus `d` times the sum of the pole divisors of the
coefficients. At a pole of order `k` of `f`, either the monic expression has a pole of order at
least `d k`, or the leading term is cancelled and some coefficient has a pole of order at least `k`.
-/
theorem nsmul_negPart_divisor_le_of_monic_eq {f : 𝕜 → 𝕜} {a : ℕ → 𝕜 → 𝕜} {d : ℕ}
    (hf : MeromorphicOn f U) (ha : ∀ j, MeromorphicOn (a j) U) :
    d • (divisor f U)⁻
      ≤ (divisor (f ^ d + ∑ j ∈ range d, a j * f ^ j) U)⁻
        + d • ∑ j ∈ range d, (divisor (a j) U)⁻ := by
  have hh : MeromorphicOn (f ^ d + ∑ j ∈ range d, a j * f ^ j) U :=
    (hf.pow d).add (MeromorphicOn.sum fun j _ ↦ (ha j).mul (hf.pow j))
  rw [Function.locallyFinsuppWithin.le_def]
  intro z
  by_cases hz : z ∈ U
  swap
  · simp [hz]
  have hdiv : ∀ j, divisor (a j) U z = (meromorphicOrderAt (a j) z).untop₀ :=
    fun j ↦ divisor_apply (ha j) hz
  simp only [Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply, divisor_apply hf hz, divisor_apply hh hz, hdiv]
  simp only [nsmul_eq_mul]
  have hpos : 0 ≤ ∑ j ∈ range d, ((meromorphicOrderAt (a j) z).untop₀)⁻ :=
    sum_nonneg fun _ _ ↦ negPart_nonneg _
  have hdpos : 0 ≤ (d : ℤ) * ∑ j ∈ range d, ((meromorphicOrderAt (a j) z).untop₀)⁻ :=
    mul_nonneg (Nat.cast_nonneg d) hpos
  have hh₀ : 0 ≤ ((meromorphicOrderAt (f ^ d + ∑ j ∈ range d, a j * f ^ j) z).untop₀)⁻ :=
    negPart_nonneg _
  cases hn : meromorphicOrderAt f z with
  | top => simpa using add_nonneg hh₀ hdpos
  | coe n =>
  obtain h0 | h0 := le_or_gt 0 n
  · -- No pole of `f` at `z`: the left-hand side vanishes.
    simp only [WithTop.untop₀_coe, negPart_eq_zero.2 h0, mul_zero]
    exact add_nonneg hh₀ hdpos
  -- Pole of order `-n` at `z`.
  simp only [WithTop.untop₀_coe, negPart_eq_neg.2 h0.le]
  by_cases hm :
    meromorphicOrderAt (f ^ d + ∑ j ∈ range d, a j * f ^ j) z ≤ ((d * n : ℤ) : WithTop ℤ)
  · -- Case 1: the monic expression has a pole of order at least `d * (-n)`.
    have hne : meromorphicOrderAt (f ^ d + ∑ j ∈ range d, a j * f ^ j) z ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hm
    lift meromorphicOrderAt (f ^ d + ∑ j ∈ range d, a j * f ^ j) z to ℤ using hne with m hm'
    rw [WithTop.coe_le_coe] at hm
    have hdn : (d : ℤ) * n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg d) h0.le
    rw [WithTop.untop₀_coe, negPart_eq_neg.2 (hm.trans hdn)]
    nlinarith
  · -- Case 2: the leading term is cancelled, so some coefficient has a pole of order `≥ -n`.
    push Not at hm
    obtain ⟨j, hj, hle⟩ :=
      exists_meromorphicOrderAt_le_of_monic_lt (hf z hz) (fun j ↦ ha j z hz) hn hm
    have hsingle := single_le_sum (f := fun i ↦ ((meromorphicOrderAt (a i) z).untop₀)⁻)
      (fun _ _ ↦ negPart_nonneg _) hj
    have hne : meromorphicOrderAt (a j) z ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
    lift meromorphicOrderAt (a j) z to ℤ using hne with m hm'
    rw [WithTop.coe_le_coe] at hle
    have hjd : (j : ℤ) < d := by exact_mod_cast mem_range.1 hj
    have hm0 : m ≤ 0 := hle.trans (mul_nonpos_of_nonneg_of_nonpos (by linarith) h0.le)
    have hmn : -n ≤ -m := by nlinarith
    simp only [WithTop.untop₀_coe, negPart_eq_neg.2 hm0] at hsingle
    have : (d : ℤ) * -n ≤ (d : ℤ) * ∑ i ∈ range d, ((meromorphicOrderAt (a i) z).untop₀)⁻ :=
      mul_le_mul_of_nonneg_left (hmn.trans hsingle) (Nat.cast_nonneg d)
    linarith

/-- In `WithTop ℤ`, every element is bounded below by minus the negative part of its
`untop₀`. -/
private lemma neg_negPart_untop₀_le (y : WithTop ℤ) : ((-(y.untop₀)⁻ : ℤ) : WithTop ℤ) ≤ y := by
  cases y with
  | top => exact le_top
  | coe k => exact WithTop.coe_le_coe.2 (by simpa using neg_le.1 (neg_le_negPart k))

open Finset in
/--
**Pole divisor of a polynomial expression**: the pole divisor of `Σ_{j≤d} a j * f ^ j` is bounded by
the sum of the pole divisors of the coefficients plus `d` times the pole divisor of `f`. Note the
factor `d` (and not `Σ_{j≤d} j`).
-/
theorem negPart_divisor_sum_mul_pow_le {f : 𝕜 → 𝕜} {a : ℕ → 𝕜 → 𝕜} {d : ℕ}
    (hf : MeromorphicOn f U) (ha : ∀ j, MeromorphicOn (a j) U) :
    (divisor (∑ j ∈ range (d + 1), a j * f ^ j) U)⁻
      ≤ ∑ j ∈ range (d + 1), (divisor (a j) U)⁻ + d • (divisor f U)⁻ := by
  have hh : MeromorphicOn (∑ j ∈ range (d + 1), a j * f ^ j) U :=
    MeromorphicOn.sum fun j _ ↦ (ha j).mul (hf.pow j)
  rw [Function.locallyFinsuppWithin.le_def]
  intro z
  by_cases hz : z ∈ U
  swap
  · simp [hz]
  have hdiv : ∀ j, divisor (a j) U z = (meromorphicOrderAt (a j) z).untop₀ :=
    fun j ↦ divisor_apply (ha j) hz
  simp only [Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply, divisor_apply hf hz, divisor_apply hh hz, hdiv]
  simp only [nsmul_eq_mul]
  have hsum₀ : 0 ≤ ∑ j ∈ range (d + 1), ((meromorphicOrderAt (a j) z).untop₀)⁻ :=
    sum_nonneg fun _ _ ↦ negPart_nonneg _
  have hdX : 0 ≤ (d : ℤ) * ((meromorphicOrderAt f z).untop₀)⁻ :=
    mul_nonneg (Nat.cast_nonneg d) (negPart_nonneg _)
  -- Every term `a j * f ^ j` has order at least `N := -(Σ (ord a j)⁻ + d (ord f)⁻)`.
  set N : ℤ := -(∑ j ∈ range (d + 1), ((meromorphicOrderAt (a j) z).untop₀)⁻
    + d * ((meromorphicOrderAt f z).untop₀)⁻) with hN
  have hterms : ∀ j ∈ range (d + 1), MeromorphicAt (a j * f ^ j) z :=
    fun j _ ↦ (ha j z hz).mul ((hf z hz).pow j)
  have hterm : ∀ j ∈ range (d + 1), (N : WithTop ℤ) ≤ meromorphicOrderAt (a j * f ^ j) z := by
    intro j hj
    have hjd : (j : ℤ) ≤ d := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hj)
    have hsingle := single_le_sum (f := fun i ↦ ((meromorphicOrderAt (a i) z).untop₀)⁻)
      (fun _ _ ↦ negPart_nonneg _) hj
    rw [meromorphicOrderAt_mul (ha j z hz) ((hf z hz).pow j), meromorphicOrderAt_pow (hf z hz)]
    cases hm : meromorphicOrderAt (a j) z with
    | top => simp
    | coe m =>
    simp only [hm, WithTop.untop₀_coe] at hsingle
    have h₁ := neg_negPart_untop₀_le (m : WithTop ℤ)
    rw [WithTop.untop₀_coe, WithTop.coe_le_coe] at h₁
    cases hn : meromorphicOrderAt f z with
    | top =>
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        simp only [Nat.cast_zero, zero_mul, add_zero, WithTop.coe_le_coe]
        linarith
      · rw [WithTop.mul_top (by exact_mod_cast hj0.ne')]
        simp
    | coe n =>
    simp only [hn, WithTop.untop₀_coe] at hN hdX
    rw [← WithTop.coe_natCast, ← WithTop.coe_mul, ← WithTop.coe_add, WithTop.coe_le_coe]
    have h₂ := neg_negPart_untop₀_le (n : WithTop ℤ)
    rw [WithTop.untop₀_coe, WithTop.coe_le_coe] at h₂
    have hn₀ : 0 ≤ n⁻ := negPart_nonneg _
    have h₃ : -(j : ℤ) * n⁻ ≤ j * n := by nlinarith
    have h₄ : -(d : ℤ) * n⁻ ≤ -(j : ℤ) * n⁻ := by nlinarith
    linarith
  have hsum : (N : WithTop ℤ) ≤ meromorphicOrderAt (∑ j ∈ range (d + 1), a j * f ^ j) z :=
    le_meromorphicOrderAt_sum hterms hterm
  cases hs : meromorphicOrderAt (∑ j ∈ range (d + 1), a j * f ^ j) z with
  | top =>
    simp only [WithTop.untop₀_top, negPart_zero]
    linarith
  | coe s =>
    rw [hs, WithTop.coe_le_coe] at hsum
    rw [WithTop.untop₀_coe]
    rcases le_or_gt 0 s with h | h
    · simp only [negPart_eq_zero.2 h]
      linarith
    · simp only [negPart_eq_neg.2 h.le]
      linarith

end MeromorphicOn
