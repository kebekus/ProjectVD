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

Mathlib targets: `Mathlib/Analysis/Meromorphic/Order.lean` (B1),
`Mathlib/Analysis/Meromorphic/Divisor.lean` (B2). Dependencies: none within the project.

## Main results

- B1, `le_meromorphicOrderAt_sum`: the order of a finite sum is at least the minimum of the
  orders of the summands.
- `exists_meromorphicOrderAt_le_of_monic_lt`: the order-level heart of B2. If `f` has order
  `n` at `z` and the monic expression `f ^ d + Σ_{j<d} a j * f ^ j` has order greater than
  `d * n`, then the leading term `f ^ d` must be cancelled by some `a j * f ^ j`, so some
  coefficient `a j` has order at most `(d - j) * n`.
- B2, `MeromorphicOn.nsmul_negPart_divisor_le_of_monic_eq`: the **pole divisor under a monic
  relation**, `d • (div f)⁻ ≤ (div (f ^ d + Σ_{j<d} a j * f ^ j))⁻ + d • Σ_{j<d} (div (a j))⁻`.

The divisor estimate B3 for quotients with a Bezout certificate (plan §4, needed for the
rational Valiron–Mohon'ko identity) will be added together with package G.
-/

@[expose] public section

open Filter Finset Function MeromorphicOn Set Topology

/-!
## Order of a Finite Sum
-/

section OrderLevel

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {x : 𝕜}

/-- The order of a finite sum is at least the minimum of the orders of the summands: if every
summand has order at least `n`, so does the sum. Finite-sum version of `meromorphicOrderAt_add`. -/
theorem le_meromorphicOrderAt_sum {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E} {n : WithTop ℤ}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x) (hn : ∀ i ∈ s, n ≤ meromorphicOrderAt (f i) x) :
    n ≤ meromorphicOrderAt (∑ i ∈ s, f i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [sum_empty, meromorphicOrderAt_eq_top_iff.2 (by simp)]
    exact le_top
  | insert a s ha ih =>
    rw [sum_insert ha]
    have hf' : ∀ i ∈ s, MeromorphicAt (f i) x := fun i hi ↦ hf i (mem_insert_of_mem hi)
    have hn' : ∀ i ∈ s, n ≤ meromorphicOrderAt (f i) x := fun i hi ↦ hn i (mem_insert_of_mem hi)
    exact (le_min (hn a (mem_insert_self a s)) (ih hf' hn')).trans
      (meromorphicOrderAt_add (hf a (mem_insert_self a s)) (MeromorphicAt.sum hf'))

/-- In `WithTop ℤ`, a strict lower bound by an integer improves to `+ 1`. -/
private lemma coe_add_one_le_of_coe_lt {m : ℤ} {y : WithTop ℤ} (h : (m : WithTop ℤ) < y) :
    ((m + 1 : ℤ) : WithTop ℤ) ≤ y := by
  cases y with
  | top => exact le_top
  | coe k => exact WithTop.coe_le_coe.2 (Int.add_one_le_iff.2 (WithTop.coe_lt_coe.1 h))

/-!
## Cancellation of the Leading Term
-/

/-- If `f` has order `n` at `z` and the monic expression `f ^ d + Σ_{j<d} a j * f ^ j` has order
greater than `d * n`, then the leading term `f ^ d` is cancelled by one of the other terms: some
coefficient `a j` has order at most `(d - j) * n`. -/
theorem exists_meromorphicOrderAt_le_of_monic_lt {f : 𝕜 → 𝕜} {a : ℕ → 𝕜 → 𝕜} {d : ℕ} {n : ℤ}
    (hf : MeromorphicAt f x) (ha : ∀ j, MeromorphicAt (a j) x) (hn : meromorphicOrderAt f x = n)
    (hh : ((d * n : ℤ) : WithTop ℤ) < meromorphicOrderAt (f ^ d + ∑ j ∈ range d, a j * f ^ j) x) :
    ∃ j ∈ range d, meromorphicOrderAt (a j) x ≤ (((d : ℤ) - j) * n : ℤ) := by
  by_contra! hcon
  have hterms : ∀ j ∈ range d, MeromorphicAt (a j * f ^ j) x := fun j _ ↦ (ha j).mul (hf.pow j)
  -- Every term `a j * f ^ j` has order at least `d * n + 1`.
  have hterm : ∀ j ∈ range d,
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
  have hsum : ((d * n + 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (∑ j ∈ range d, a j * f ^ j) x :=
    le_meromorphicOrderAt_sum hterms hterm
  have key : ((d * n + 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (f ^ d) x := by
    rw [show f ^ d = (f ^ d + ∑ j ∈ range d, a j * f ^ j) + -(∑ j ∈ range d, a j * f ^ j) from
      (add_neg_cancel_right _ _).symm]
    refine (le_min (coe_add_one_le_of_coe_lt hh) ?_).trans
      (meromorphicOrderAt_add ((hf.pow d).add (MeromorphicAt.sum hterms))
        (MeromorphicAt.sum hterms).neg)
    rwa [← meromorphicOrderAt_neg]
  -- But `f ^ d` has order exactly `d * n`.
  rw [meromorphicOrderAt_pow hf, hn, ← WithTop.coe_natCast (α := ℤ), ← WithTop.coe_mul,
    WithTop.coe_le_coe] at key
  omega

end OrderLevel

/-!
## The Pole Divisor under a Monic Relation
-/

namespace MeromorphicOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜}

/-- **Pole divisor under a monic relation**, weighted form: `d` times the pole divisor of `f`
is bounded by the pole divisor of `f ^ d + Σ_{j<d} a j * f ^ j` plus `d` times the sum of the
pole divisors of the coefficients. At a pole of order `k` of `f`, either the monic expression
has a pole of order at least `d k`, or the leading term is cancelled and some coefficient has
a pole of order at least `k`. -/
theorem nsmul_negPart_divisor_le_of_monic_eq {f : 𝕜 → 𝕜} {a : ℕ → 𝕜 → 𝕜} {d : ℕ}
    (hf : MeromorphicOn f U) (ha : ∀ j, MeromorphicOn (a j) U) :
    d • (divisor f U)⁻
      ≤ (divisor (f ^ d + ∑ j ∈ range d, a j * f ^ j) U)⁻
        + d • ∑ j ∈ range d, (divisor (a j) U)⁻ := by
  have hh : MeromorphicOn (f ^ d + ∑ j ∈ range d, a j * f ^ j) U :=
    (hf.pow d).add (MeromorphicOn.sum fun j _ ↦ (ha j).mul (hf.pow j))
  rw [locallyFinsuppWithin.le_def]
  intro z
  by_cases hz : z ∈ U
  swap
  · simp [hz]
  have hdiv : ∀ j, divisor (a j) U z = (meromorphicOrderAt (a j) z).untop₀ :=
    fun j ↦ divisor_apply (ha j) hz
  simp only [locallyFinsuppWithin.coe_nsmul, Pi.smul_apply, locallyFinsuppWithin.coe_add,
    Pi.add_apply, locallyFinsuppWithin.negPart_apply, locallyFinsuppWithin.coe_sum,
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

end MeromorphicOn
