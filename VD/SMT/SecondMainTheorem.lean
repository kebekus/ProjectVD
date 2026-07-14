/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.SMT.SecondMainTheoremRamification

/-!
# The Second Main Theorem, Truncated Form — SMT work package F

See `VD/SMT/PLAN-SecondMainTheorem.md`, §8.

Mathlib target: `Mathlib/Analysis/Complex/ValueDistribution/SecondMainTheorem.lean`
(part 3 of 3).
Dependencies: `VD/SMT/TruncatedCounting.lean` (package A), `VD/SMT/DivisorDeriv.lean`
(package B), `VD/SMT/SecondMainTheoremRamification.lean` (package E).

This file proves the **Second Main Theorem** of value distribution theory in its classical
truncated form: for `f` meromorphic on `ℂ` and a finite set `S : Finset (WithTop ℂ)` of
targets,

```
(#S − 2) · T(r, f)  ≤  Σ_{a ∈ S} N̄(r, a)  +  O(log⁺ T(r, f) + log r)
```

as `r → ∞` outside a set of finite Lebesgue measure, where `N̄` denotes the truncated
counting function introduced in `VD/SMT/TruncatedCounting.lean`.  The result carries **no**
hypothesis beyond meromorphy of `f`: there is no nondegeneracy assumption on `f`, no
distinctness assumption on the targets (a `Finset` is distinct by construction), and no
cardinality assumption on `S`.

## Main results

- `ValueDistribution.secondMainTheorem`: the Second Main Theorem, truncated form (S2).

- `ValueDistribution.secondMainTheorem_posPart`: the `posPart` reformulation (S2′), a
  filter-algebra-composable `IsBigO` statement.

- Helpers flagged for possible upstreaming into `FirstMainTheorem.lean`:
  `ValueDistribution.characteristic_coe_eq_characteristic_shift_inv` and the combined First
  Main Theorem, `ValueDistribution.exists_abs_characteristic_coe_sub_characteristic_top_le`
  (`|T(r, a) − T(r, ∞)| ≤ C`).

The proof combines the Second Main Theorem with ramification term (S1, package E) with the
First Main Theorem to convert proximity into counting functions, and then absorbs the
multiplicity excess into the ramification term using the two counting inequalities of
package B.

References: [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677], Theorem
VII.2.2; [Hayman, *Meromorphic Functions*][MR164038], §2.3.
-/

open Asymptotics Filter MeasureTheory Metric Real Set Topology

namespace ValueDistribution

/-!
## The First Main Theorem, Combined Form

The two helpers below combine both parts of the First Main Theorem into the statement that
the characteristic functions of `f` for a finite value and for `⊤` agree up to a bounded
function.  They are flagged for possible upstreaming into
`Mathlib/Analysis/Complex/ValueDistribution/FirstMainTheorem.lean`.
-/

/--
The characteristic function of `f` for a finite value `a₀` is the characteristic function
of the shifted inverse `(f - a₀)⁻¹` for the value `⊤`.
-/
lemma characteristic_coe_eq_characteristic_shift_inv {f : ℂ → ℂ} {a₀ : ℂ} :
    characteristic f a₀ = characteristic (f · - a₀)⁻¹ ⊤ := by
  have h₁ : proximity f ↑a₀ = proximity (f · - a₀)⁻¹ ⊤ := by
    rw [proximity_inv, proximity_coe, proximity_zero]
  have h₂ : logCounting f ↑a₀ = logCounting (f · - a₀)⁻¹ ⊤ := by
    rw [logCounting_inv, logCounting_coe, logCounting_zero]
  unfold characteristic
  rw [h₁, h₂]

/--
**First Main Theorem, combined form**: for every finite value `a₀`, the characteristic
functions `characteristic f a₀` and `characteristic f ⊤` differ by a bounded function.
-/
theorem exists_abs_characteristic_coe_sub_characteristic_top_le {f : ℂ → ℂ}
    (hf : Meromorphic f) (a₀ : ℂ) :
    ∃ C, ∀ r, |characteristic f a₀ r - characteristic f ⊤ r| ≤ C := by
  have hshift : Meromorphic (f · - a₀) := by fun_prop
  refine ⟨max |log ‖f 0 - a₀‖| |log ‖meromorphicTrailingCoeffAt (f · - a₀) 0‖|
    + (log⁺ ‖a₀‖ + log 2), fun r ↦ ?_⟩
  -- First part of the FMT, for the shifted function `f - a₀` …
  have h₁ := characteristic_sub_characteristic_inv_le (R := r) hshift
  -- … and the second part, for the shift itself.
  have h₂ := abs_characteristic_sub_characteristic_shift_le (a₀ := a₀) (r := r) hf
  have h₃ := abs_sub_le (characteristic (f · - a₀)⁻¹ ⊤ r) (characteristic (f · - a₀) ⊤ r)
    (characteristic f ⊤ r)
  rw [characteristic_coe_eq_characteristic_shift_inv]
  rw [abs_sub_comm] at h₁ h₂
  linarith

/-!
## The Second Main Theorem
-/

/--
Auxiliary version of the Second Main Theorem, with the finite targets given as a
`Finset ℂ` and the value `⊤` always counted: for `f` meromorphic on `ℂ`,

`(#s + 1 − 2) T(r, f) ≤ Σₐ N̄(r, a) + N̄(r, ⊤) + c (log⁺ T(r, f) + log r)`

for all sufficiently large `r` outside a set of finite Lebesgue measure.  The public
statement `secondMainTheorem` below is derived from this by `Finset (WithTop ℂ)`
bookkeeping.
-/
private lemma secondMainTheorem_aux {f : ℂ → ℂ} (hf : Meromorphic f) (s : Finset ℂ) :
    ∃ c, ∀ᶠ r in volume.cofinite ⊓ atTop,
      ((s.card : ℝ) - 1) * characteristic f ⊤ r
        ≤ ∑ a ∈ s, truncatedLogCounting f a r + truncatedLogCounting f ⊤ r
          + c * (log⁺ (characteristic f ⊤ r) + Real.log r) := by
  -- The Second Main Theorem with ramification term (S1) …
  obtain ⟨c₀, hc₀⟩ := secondMainTheorem_ramification hf s
  -- … and one combined FMT constant for every target.
  choose C hC using fun a : ℂ ↦ exists_abs_characteristic_coe_sub_characteristic_top_le hf a
  refine ⟨c₀ + max (∑ a ∈ s, C a) 0, ?_⟩
  filter_upwards [hc₀, mem_inf_of_right (eventually_ge_atTop (Real.exp 1))] with r hS1 hre
  have hr1 : (1 : ℝ) ≤ r := by linarith [Real.add_one_le_exp 1]
  have hlogr : 1 ≤ Real.log r := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hre
  have hv1 : 1 ≤ log⁺ (characteristic f ⊤ r) + Real.log r := by
    linarith [posLog_nonneg (x := characteristic f ⊤ r)]
  -- `T(r) = m(r, ∞) + N(r, ∞)`, definitionally.
  have hT : characteristic f ⊤ r = proximity f ⊤ r + logCounting f ⊤ r := rfl
  -- Combined FMT: convert the proximity for each target into the characteristic.
  have hprox : ∀ a ∈ s, characteristic f ⊤ r - C a - logCounting f a r ≤ proximity f a r := by
    intro a _
    have h₁ := (abs_le.1 (hC a r)).1
    have h₂ : characteristic f a r = proximity f a r + logCounting f a r := rfl
    linarith
  have hsum : (s.card : ℝ) * characteristic f ⊤ r - (∑ a ∈ s, C a)
      - ∑ a ∈ s, logCounting f a r ≤ ∑ a ∈ s, proximity f a r := by
    calc (s.card : ℝ) * characteristic f ⊤ r - (∑ a ∈ s, C a) - ∑ a ∈ s, logCounting f a r
        = ∑ a ∈ s, (characteristic f ⊤ r - C a - logCounting f a r) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ s, proximity f a r := Finset.sum_le_sum hprox
  -- Package B: the multiplicity excess over the truncation is absorbed by `N(r, 1/f′)` …
  have hB1 : (∑ a ∈ s, logCounting f a r) - ∑ a ∈ s, truncatedLogCounting f a r
      ≤ logCounting (deriv f) 0 r := by
    rw [← Finset.sum_sub_distrib]
    exact sum_logCounting_sub_truncatedLogCounting_le hf s hr1
  -- … and the pole divisor of `deriv f` produces the truncated counting function at `⊤`.
  have hB2 : logCounting (deriv f) ⊤ r = logCounting f ⊤ r + truncatedLogCounting f ⊤ r := by
    rw [logCounting_deriv_top hf]
    rfl
  -- Absorb the additive FMT constants into the error term.
  have habs : ∑ a ∈ s, C a
      ≤ max (∑ a ∈ s, C a) 0 * (log⁺ (characteristic f ⊤ r) + Real.log r) := by
    calc ∑ a ∈ s, C a
        ≤ max (∑ a ∈ s, C a) 0 * 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ max (∑ a ∈ s, C a) 0 * (log⁺ (characteristic f ⊤ r) + Real.log r) :=
          mul_le_mul_of_nonneg_left hv1 (le_max_right _ _)
  linarith [hS1, hT, hsum, hB1, hB2, habs]

/--
**Second Main Theorem** of value distribution theory, truncated form: if `f` is meromorphic
on `ℂ` and `S` is a finite set of targets in `ℂ ∪ {∞}`, then

`(#S − 2) T(r, f) ≤ Σ_{a ∈ S} N̄(r, a) + c (log⁺ T(r, f) + log r)`

for all sufficiently large `r` outside a set of finite Lebesgue measure, where `N̄` is the
truncated logarithmic counting function, which counts zeros/poles without multiplicity.
No hypothesis beyond meromorphy of `f` is needed.
-/
theorem secondMainTheorem {f : ℂ → ℂ} (hf : Meromorphic f) (S : Finset (WithTop ℂ)) :
    ∃ c, ∀ᶠ r in volume.cofinite ⊓ atTop,
      (S.card - 2 : ℝ) * characteristic f ⊤ r
        ≤ ∑ a ∈ S, truncatedLogCounting f a r
          + c * (log⁺ (characteristic f ⊤ r) + Real.log r) := by
  classical
  -- The finite targets of `S`, as a `Finset ℂ`.
  set s : Finset ℂ := (S.erase ⊤).preimage (↑·) WithTop.coe_injective.injOn with hs
  have hrange : ∀ x ∈ S.erase ⊤, x ∈ Set.range ((↑·) : ℂ → WithTop ℂ) := fun x hx ↦
    WithTop.ne_top_iff_exists.1 (Finset.ne_of_mem_erase hx)
  have hsum : ∀ r, ∑ a ∈ s, truncatedLogCounting f ↑a r
      = ∑ a ∈ S.erase ⊤, truncatedLogCounting f a r := by
    intro r
    rw [hs]
    exact Finset.sum_preimage _ _ _ (fun a ↦ truncatedLogCounting f a r)
      fun x hx hxr ↦ absurd (hrange x hx) hxr
  have hcard : s.card = (S.erase ⊤).card := by
    rw [hs, Finset.card_preimage]
    congr 1
    exact Finset.filter_true_of_mem hrange
  obtain ⟨c, hc⟩ := secondMainTheorem_aux hf s
  refine ⟨c, ?_⟩
  filter_upwards [hc, mem_inf_of_right (eventually_ge_atTop 1)] with r haux hr1
  by_cases htop : ⊤ ∈ S
  -- If `⊤ ∈ S`, the auxiliary statement is exactly the claim.
  · have hcard' : (S.card : ℝ) = (s.card : ℝ) + 1 := by
      have h₁ : 1 ≤ S.card := Finset.card_pos.2 ⟨⊤, htop⟩
      have h₂ : s.card = S.card - 1 := by rw [hcard, Finset.card_erase_of_mem htop]
      exact_mod_cast (by omega : S.card = s.card + 1)
    have hsplit : truncatedLogCounting f ⊤ r + ∑ a ∈ S.erase ⊤, truncatedLogCounting f a r
        = ∑ a ∈ S, truncatedLogCounting f a r :=
      Finset.add_sum_erase S (fun a ↦ truncatedLogCounting f a r) htop
    rw [hcard']
    linarith [haux, hsum r, hsplit]
  -- If `⊤ ∉ S`, drop the `⊤`-term of the auxiliary statement, trading it against one
  -- characteristic function on the left: `N̄(r, ⊤) ≤ N(r, ⊤) ≤ T(r)`.
  · have herase : S.erase ⊤ = S := Finset.erase_eq_of_notMem htop
    have hcard' : (S.card : ℝ) = (s.card : ℝ) := by rw [hcard, herase]
    have hNbar : truncatedLogCounting f ⊤ r ≤ characteristic f ⊤ r := by
      have h₁ : truncatedLogCounting f ⊤ r ≤ logCounting f ⊤ r := truncatedLogCounting_le hr1
      have h₂ : (0 : ℝ) ≤ proximity f ⊤ r := proximity_nonneg r
      have h₃ : characteristic f ⊤ r = proximity f ⊤ r + logCounting f ⊤ r := rfl
      linarith
    have hsumS : ∑ a ∈ s, truncatedLogCounting f ↑a r = ∑ a ∈ S, truncatedLogCounting f a r := by
      rw [hsum r, herase]
    rw [hcard']
    linarith [haux, hNbar, hsumS]

/--
**Second Main Theorem**, `posPart` reformulation: the positive part of the defect of the
truncated Second Main Theorem inequality is `O(log⁺ T(r, f) + log r)` along
`volume.cofinite ⊓ atTop`.  This form composes conveniently with the filter algebra of
`Asymptotics.IsBigO`.
-/
theorem secondMainTheorem_posPart {f : ℂ → ℂ} (hf : Meromorphic f) (S : Finset (WithTop ℂ)) :
    (fun r ↦ ((S.card - 2 : ℝ) * characteristic f ⊤ r
        - ∑ a ∈ S, truncatedLogCounting f a r)⁺)
      =O[volume.cofinite ⊓ atTop] fun r ↦ log⁺ (characteristic f ⊤ r) + Real.log r := by
  obtain ⟨c, hc⟩ := secondMainTheorem hf S
  rw [isBigO_iff]
  refine ⟨max c 0, ?_⟩
  filter_upwards [hc, mem_inf_of_right (eventually_ge_atTop (Real.exp 1))] with r h₁ hre
  have hlogr : 1 ≤ Real.log r := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hre
  have hv0 : 0 ≤ log⁺ (characteristic f ⊤ r) + Real.log r := by
    linarith [posLog_nonneg (x := characteristic f ⊤ r)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (posPart_nonneg _),
    abs_of_nonneg hv0, posPart_def]
  apply sup_le
  · have h₂ : c * (log⁺ (characteristic f ⊤ r) + Real.log r)
        ≤ max c 0 * (log⁺ (characteristic f ⊤ r) + Real.log r) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hv0
    linarith
  · exact mul_nonneg (le_max_right _ _) hv0

end ValueDistribution
