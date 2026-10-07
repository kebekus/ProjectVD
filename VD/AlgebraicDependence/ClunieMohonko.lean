/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
public import VD.AlgebraicDependence.GrowthClass
public import VD.AlgebraicDependence.PointwiseEstimates
public import VD.LLD.LogDerivEstimates

/-!
# Clunie's Lemma and Mohon'ko's Lemma — Algebraic Dependence work package E

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §7.

Mathlib target: new file `Mathlib/Analysis/Complex/ValueDistribution/Clunie.lean`.
Dependencies: package A and `circleAverage_mono_codiscreteWithin`
(`VD/LLD/LogDerivEstimates.lean`).

Both results are the algebraic (derivative-free) cases of Laine, Chapter 2.4; the differential
versions are a follow-up (plan §10). Throughout, `f : ℂ → ℂ` is meromorphic, `a b : ℕ → ℂ → ℂ`
are families of meromorphic coefficients, and `∑ j ∈ range (p + 1), a j * f ^ j` is the
polynomial expression of degree `p` in `f` with coefficients `a j`.

## Main results

- T4, `ValueDistribution.proximity_le_of_pow_mul_eq`: **Clunie's lemma**: if
  `f ^ n * P(f) =ᶠ[codiscrete ℂ] Q(f)` with `deg Q ≤ n`, then
  `m(r, P(f)) ≤ Σ m(r, coefficients of P) + Σ m(r, coefficients of Q) + log (max (p+1) (n+1))`.
- T5, `ValueDistribution.proximity_zero_le_of_eq_zero`: **Mohon'ko's lemma**: if
  `P(f) =ᶠ[codiscrete ℂ] 0` with constant coefficient `a 0` not codiscretely zero, then
  `m(r, 1/f) ≤ m(r, 1/a 0) + Σ_{j≥1} m(r, a j) + log d`.
- `ValueDistribution.proximity_mem_of_pow_mul_eq`,
  `ValueDistribution.proximity_zero_mem_of_eq_zero`: the growth-class forms. With coefficients
  in the field of small functions `S(f)`, these read `m(r, P(f)) = S(r, f)` and
  `m(r, 1/f) = S(r, f)`.
- `ValueDistribution.exists_abs_characteristic_sub_logCounting_zero_le_of_eq_zero`: under the
  hypotheses of Mohon'ko's lemma, the zeros of `f` carry its characteristic:
  `N(r, 1/f) = T(r, f) + S(r, f)`.
-/

@[expose] public section

open Filter Finset Function Real Set Topology

namespace ValueDistribution

variable {f : ℂ → ℂ} {a b : ℕ → ℂ → ℂ} {d n p : ℕ}

/-!
## Clunie's Lemma
-/

/-- **Clunie's lemma** (T4), algebraic case: if `f ^ n * P(f) = Q(f)` away from a discrete
set, where `P = Σ_{j≤p} a j * X ^ j` and `Q = Σ_{k≤n} b k * X ^ k` has degree at most `n`,
then the proximity function of `P(f)` is bounded by the proximity functions of the
coefficients of `P` and `Q`:
`m(r, P(f)) ≤ Σ_{j≤p} m(r, a j) + Σ_{k≤n} m(r, b k) + log (max (p + 1) (n + 1))`. -/
theorem proximity_le_of_pow_mul_eq (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j))
    (hb : ∀ k, Meromorphic (b k))
    (h : f ^ n * (∑ j ∈ range (p + 1), a j * f ^ j)
      =ᶠ[codiscrete ℂ] ∑ k ∈ range (n + 1), b k * f ^ k) {r : ℝ} (hr : r ≠ 0) :
    proximity (∑ j ∈ range (p + 1), a j * f ^ j) ⊤ r
      ≤ ∑ j ∈ range (p + 1), proximity (a j) ⊤ r + ∑ k ∈ range (n + 1), proximity (b k) ⊤ r
        + log (max (p + 1) (n + 1)) := by
  have hint : ∀ {u : ℂ → ℂ}, Meromorphic u → CircleIntegrable (fun z ↦ log⁺ ‖u z‖) 0 r :=
    fun hu ↦ hu.meromorphicOn.circleIntegrable_posLog_norm
  have hA : ∀ j ∈ range (p + 1), CircleIntegrable (fun z ↦ log⁺ ‖a j z‖) 0 r :=
    fun j _ ↦ hint (ha j)
  have hB : ∀ k ∈ range (n + 1), CircleIntegrable (fun z ↦ log⁺ ‖b k z‖) 0 r :=
    fun k _ ↦ hint (hb k)
  have hSA := CircleIntegrable.sum (range (p + 1)) hA
  have hSB := CircleIntegrable.sum (range (n + 1)) hB
  have hP := hint (Meromorphic.sum fun j _ ↦ (ha j).mul hf.pow :
    Meromorphic (∑ j ∈ range (p + 1), a j * f ^ j))
  have hC : CircleIntegrable (fun _ : ℂ ↦ log (max (p + 1 : ℝ) (n + 1))) 0 r :=
    circleIntegrable_const _ _ _
  simp only [proximity_top]
  -- The pointwise estimate, integrated where the relation holds.
  have key : circleAverage (fun z ↦ log⁺ ‖(∑ j ∈ range (p + 1), a j * f ^ j) z‖) 0 r
      ≤ circleAverage (∑ j ∈ range (p + 1), (fun z ↦ log⁺ ‖a j z‖)
          + ∑ k ∈ range (n + 1), (fun z ↦ log⁺ ‖b k z‖)
          + fun _ ↦ log (max (p + 1 : ℝ) (n + 1))) 0 r := by
    apply circleAverage_mono_codiscreteWithin hr hP ((hSA.add hSB).add hC)
    filter_upwards [h.filter_mono (codiscreteWithin_mono (subset_univ _))] with z hz
    simp only [Pi.add_apply, Finset.sum_apply]
    exact posLog_norm_le_of_pow_mul_eq (a := fun j ↦ a j z) (b := fun k ↦ b k z)
      (by simpa [Finset.sum_apply] using hz)
  rwa [circleAverage_add (hSA.add hSB) hC, circleAverage_add hSA hSB, circleAverage_sum hA,
    circleAverage_sum hB, circleAverage_const] at key

/-- **Clunie's lemma, growth-class form**: if the coefficients of `P` and `Q` have
characteristic in the growth class `G` and `f ^ n * P(f) = Q(f)` away from a discrete set with
`deg Q ≤ n`, then `m(r, P(f))` lies in `G`. For the little-o class
`(· =o[volume.cofinite ⊓ atTop] T(r, f))` this is the classical `m(r, P(f)) = S(r, f)`. -/
theorem proximity_mem_of_pow_mul_eq {l : Filter ℝ} {G : (ℝ → ℝ) → Prop} (hG : IsGrowthClass l G)
    (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j)) (hb : ∀ k, Meromorphic (b k))
    (ha' : ∀ j ∈ range (p + 1), G (characteristic (a j) ⊤))
    (hb' : ∀ k ∈ range (n + 1), G (characteristic (b k) ⊤))
    (h : f ^ n * (∑ j ∈ range (p + 1), a j * f ^ j)
      =ᶠ[codiscrete ℂ] ∑ k ∈ range (n + 1), b k * f ^ k) :
    G (proximity (∑ j ∈ range (p + 1), a j * f ^ j) ⊤) := by
  refine hG.of_le (v := ∑ j ∈ range (p + 1), characteristic (a j) ⊤
      + ∑ k ∈ range (n + 1), characteristic (b k) ⊤ + fun _ ↦ log (max (p + 1 : ℝ) (n + 1)))
    (hG.add (hG.add (hG.sum ha') (hG.sum hb')) (hG.const _))
    (Eventually.of_forall fun r ↦ proximity_nonneg r) ?_
  filter_upwards [hG.le_atTop (eventually_ge_atTop 1)] with r hr
  simp only [Pi.add_apply, Finset.sum_apply]
  calc proximity (∑ j ∈ range (p + 1), a j * f ^ j) ⊤ r
      ≤ ∑ j ∈ range (p + 1), proximity (a j) ⊤ r + ∑ k ∈ range (n + 1), proximity (b k) ⊤ r
        + log (max (p + 1) (n + 1)) :=
        proximity_le_of_pow_mul_eq hf ha hb h (zero_lt_one.trans_le hr).ne'
    _ ≤ _ := by
        gcongr with j _ k _
        · exact proximity_le_characteristic hr
        · exact proximity_le_characteristic hr

/-!
## Mohon'ko's Lemma
-/

/-- **Mohon'ko's lemma** (T5), algebraic case: if `P(f) = 0` away from a discrete set, where
`P = Σ_{j≤d} a j * X ^ j` has constant coefficient `a 0` not codiscretely zero, then the
proximity function of `f` at `0` is bounded by the proximity functions of the coefficients:
`m(r, 1/f) ≤ m(r, 1/a 0) + Σ_{1≤j≤d} m(r, a j) + log d`. -/
theorem proximity_zero_le_of_eq_zero (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j))
    (h : ∑ j ∈ range (d + 1), a j * f ^ j =ᶠ[codiscrete ℂ] 0) (h₀ : ¬ a 0 =ᶠ[codiscrete ℂ] 0)
    {r : ℝ} (hr : r ≠ 0) :
    proximity f 0 r
      ≤ proximity (a 0) 0 r + ∑ j ∈ Finset.Ico 1 (d + 1), proximity (a j) ⊤ r + log d := by
  -- The constant coefficient does not vanish on a codiscrete set.
  have hne : ∀ᶠ z in codiscrete ℂ, a 0 z ≠ 0 := by
    have h : ∀ z, meromorphicOrderAt (a 0) z ≠ ⊤ := by
      have := (ha 0).exists_meromorphicOrderAt_eq_top_iff_eventually_zero.not.2 h₀
      push Not at this
      exact this
    exact (ha 0).meromorphicOn.eventually_codiscreteWithin_apply_ne_zero fun z _ ↦ h z
  have hint : ∀ {u : ℂ → ℂ}, Meromorphic u → CircleIntegrable (fun z ↦ log⁺ ‖u z‖) 0 r :=
    fun hu ↦ hu.meromorphicOn.circleIntegrable_posLog_norm
  have hA : ∀ j ∈ Finset.Ico 1 (d + 1), CircleIntegrable (fun z ↦ log⁺ ‖a j z‖) 0 r :=
    fun j _ ↦ hint (ha j)
  have hSA := CircleIntegrable.sum (Finset.Ico 1 (d + 1)) hA
  have hF := hint hf.inv
  have hA₀ := hint (ha 0).inv
  have hC : CircleIntegrable (fun _ : ℂ ↦ log (d : ℝ)) 0 r := circleIntegrable_const _ _ _
  simp only [proximity_zero_of_complexValued, proximity_top]
  -- The pointwise estimate, integrated where the relation holds and `a 0` does not vanish.
  have key : circleAverage (fun z ↦ log⁺ ‖f⁻¹ z‖) 0 r
      ≤ circleAverage ((fun z ↦ log⁺ ‖(a 0)⁻¹ z‖)
          + ∑ j ∈ Finset.Ico 1 (d + 1), (fun z ↦ log⁺ ‖a j z‖) + fun _ ↦ log (d : ℝ)) 0 r := by
    apply circleAverage_mono_codiscreteWithin hr hF ((hA₀.add hSA).add hC)
    filter_upwards [h.filter_mono (codiscreteWithin_mono (subset_univ _)),
      hne.filter_mono (codiscreteWithin_mono (subset_univ _))] with z hz hz₀
    simp only [Pi.add_apply, Pi.inv_apply, Finset.sum_apply, norm_inv]
    exact posLog_norm_inv_le_of_eq_zero (a := fun j ↦ a j z)
      (by simpa [Finset.sum_apply] using hz) hz₀
  rwa [circleAverage_add (hA₀.add hSA) hC, circleAverage_add hA₀ hSA, circleAverage_sum hA,
    circleAverage_const] at key

/-- **Mohon'ko's lemma, growth-class form**: if the coefficients of `P` have characteristic in
the growth class `G`, `P(f) = 0` away from a discrete set, and the constant coefficient of `P`
is not codiscretely zero, then `m(r, 1/f)` lies in `G`. For the little-o class
`(· =o[volume.cofinite ⊓ atTop] T(r, f))` this is the classical `m(r, 1/f) = S(r, f)`. -/
theorem proximity_zero_mem_of_eq_zero {l : Filter ℝ} {G : (ℝ → ℝ) → Prop}
    (hG : IsGrowthClass l G) (hf : Meromorphic f) (ha : ∀ j, Meromorphic (a j))
    (ha' : ∀ j ∈ range (d + 1), G (characteristic (a j) ⊤))
    (h : ∑ j ∈ range (d + 1), a j * f ^ j =ᶠ[codiscrete ℂ] 0) (h₀ : ¬ a 0 =ᶠ[codiscrete ℂ] 0) :
    G (proximity f 0) := by
  set c := max |log ‖a 0 0‖| |log ‖meromorphicTrailingCoeffAt (a 0) 0‖| with hc
  refine hG.of_le (v := characteristic (a 0) ⊤
      + ∑ j ∈ Finset.Ico 1 (d + 1), characteristic (a j) ⊤ + fun _ ↦ c + log (d : ℝ))
    (hG.add (hG.add (ha' 0 (mem_range.2 (Nat.succ_pos d)))
      (hG.sum fun j hj ↦ ha' j (mem_range.2 (mem_Ico.1 hj).2))) (hG.const _))
    (Eventually.of_forall fun r ↦ proximity_nonneg r) ?_
  filter_upwards [hG.le_atTop (eventually_ge_atTop 1)] with r hr
  simp only [Pi.add_apply, Finset.sum_apply]
  -- The First Main Theorem bounds `m(r, 1/a 0)` by `T(r, a 0) + c`.
  have h₁ : proximity (a 0) 0 r ≤ characteristic (a 0) ⊤ r + c := by
    rw [← proximity_inv]
    linarith [proximity_le_characteristic (f := (a 0)⁻¹) (a := ⊤) hr,
      (abs_le.1 (characteristic_sub_characteristic_inv_le (ha 0) (R := r))).1]
  have h₂ : ∑ j ∈ Finset.Ico 1 (d + 1), proximity (a j) ⊤ r
      ≤ ∑ j ∈ Finset.Ico 1 (d + 1), characteristic (a j) ⊤ r :=
    sum_le_sum fun j _ ↦ proximity_le_characteristic hr
  linarith [proximity_zero_le_of_eq_zero hf ha h h₀ (zero_lt_one.trans_le hr).ne']

/-- Under the hypotheses of Mohon'ko's lemma, the zeros of `f` carry its characteristic:
`N(r, 1/f) = T(r, f) + u(r)` with `u ∈ G`. For the little-o class this is the classical
`N(r, 1/f) = T(r, f) + S(r, f)`, i.e. `f` has deficiency zero at `0`. -/
theorem exists_abs_characteristic_sub_logCounting_zero_le_of_eq_zero {l : Filter ℝ}
    {G : (ℝ → ℝ) → Prop} (hG : IsGrowthClass l G) (hf : Meromorphic f)
    (ha : ∀ j, Meromorphic (a j)) (ha' : ∀ j ∈ range (d + 1), G (characteristic (a j) ⊤))
    (h : ∑ j ∈ range (d + 1), a j * f ^ j =ᶠ[codiscrete ℂ] 0) (h₀ : ¬ a 0 =ᶠ[codiscrete ℂ] 0) :
    ∃ u, G u ∧ ∀ᶠ r in l, |characteristic f ⊤ r - logCounting f 0 r| ≤ u r := by
  set c := max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖| with hc
  refine ⟨proximity f 0 + fun _ ↦ c,
    hG.add (proximity_zero_mem_of_eq_zero hG hf ha ha' h h₀) (hG.const c), ?_⟩
  filter_upwards [hG.le_atTop (eventually_ge_atTop 1)] with r hr
  simp only [Pi.add_apply]
  -- `T(r, 1/f) = m(r, 1/f) + N(r, 1/f)` and the First Main Theorem.
  have h₁ : characteristic f⁻¹ ⊤ r = proximity f 0 r + logCounting f 0 r := by
    simp [characteristic, proximity_inv, logCounting_inv]
  have h₂ := abs_le.1 (characteristic_sub_characteristic_inv_le hf (R := r))
  have h₃ : 0 ≤ proximity f 0 r := proximity_nonneg r
  rw [abs_le]
  constructor <;> linarith

end ValueDistribution
