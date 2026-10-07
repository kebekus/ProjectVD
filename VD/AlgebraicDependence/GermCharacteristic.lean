/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
public import VD.AlgebraicDependence.MonicRelation
public import VD.Field.GermFieldAPI

/-!
# The Characteristic of a Meromorphic Germ — Algebraic Dependence work packages F0–F1

See `VD/AlgebraicDependence/PLAN-AlgebraicDependence.md`, §8.

Mathlib target: follows the germ field `VD/Field/` upstream. Dependencies: `VD/Field/`,
package C (for the hypothesis-free product bound C0).

Throughout, `K := MeromorphicOn.germRing ℂ Set.univ` is the field of germs of meromorphic
functions on `ℂ`. The Nevanlinna characteristic of a germ is defined through its chosen
representative `MeromorphicOn.GermRing.out`; for `r ≠ 0` it does not depend on the choice
(`characteristic_congr_codiscrete`), so the arithmetic of the characteristic on functions
transports to germs verbatim.

## Main definitions and results

- F0: `Fact` instances making `germRing ℂ univ` a field and a `ℂ`-algebra globally;
  `MeromorphicOn.GermRing.toGerm`, the germ of a meromorphic function.
- F1: `MeromorphicOn.GermRing.characteristic : germRing ℂ univ → ℝ → ℝ`, with
  `characteristic_toGerm` (independence of the representative for `r ≠ 0`), and the transported
  arithmetic `characteristic_nonneg`, `characteristic_add_le`, `characteristic_sum_le`,
  `characteristic_mul_le`, `characteristic_pow`, `exists_abs_characteristic_inv_sub_le`,
  `characteristic_algebraMap`, `characteristic_neg`.
- The germ-level **algebraic dependence bound**
  `characteristic_le_sum_characteristic_of_monic_eq_zero` (T2 for germs), the input for the
  relative algebraic closedness of growth fields in package F3.
-/

@[expose] public section

open Filter Finset Function Real Set Topology

/-!
## Instances for `U = univ`
-/

instance : Fact (IsPreconnected (Set.univ : Set ℂ)) := ⟨isPreconnected_univ⟩

instance : Fact (Set.univ : Set ℂ).Nontrivial := ⟨Set.nontrivial_univ⟩

namespace MeromorphicOn.GermRing

/-- The germ of a meromorphic function on `ℂ`. -/
noncomputable abbrev toGerm {f : ℂ → ℂ} (hf : Meromorphic f) : germRing ℂ univ :=
  ⟨(f : Germ (codiscreteWithin (univ : Set ℂ)) ℂ), coe_mem_germRing hf.meromorphicOn⟩

@[simp]
theorem coe_toGerm {f : ℂ → ℂ} (hf : Meromorphic f) :
    ((toGerm hf : germRing ℂ univ) : Germ (codiscreteWithin (univ : Set ℂ)) ℂ)
      = (f : Germ (codiscreteWithin (univ : Set ℂ)) ℂ) := rfl

/-- A meromorphic function agrees with the chosen representative of its germ away from a
discrete set. -/
theorem eventuallyEq_out_toGerm {f : ℂ → ℂ} (hf : Meromorphic f) :
    f =ᶠ[codiscrete ℂ] out (toGerm hf) :=
  out_eventuallyEq rfl

/-- The chosen representative of a germ in `germRing ℂ univ` is meromorphic on `ℂ`. -/
theorem meromorphic_out (a : germRing ℂ univ) : Meromorphic (out a) :=
  meromorphicOn_univ.1 (meromorphicOn_out a)

/-!
## The Characteristic of a Germ
-/

/-- The Nevanlinna characteristic of a meromorphic germ on `ℂ`, defined through the chosen
representative. For `r ≠ 0` it does not depend on the representative, see
`characteristic_toGerm`. -/
noncomputable def characteristic (a : germRing ℂ univ) : ℝ → ℝ :=
  ValueDistribution.characteristic (out a) ⊤

/-- The characteristic of a germ is the characteristic of any of its representatives, for
`r ≠ 0`. -/
theorem characteristic_toGerm {f : ℂ → ℂ} (hf : Meromorphic f) {r : ℝ} (hr : r ≠ 0) :
    characteristic (toGerm hf) r = ValueDistribution.characteristic f ⊤ r :=
  (ValueDistribution.characteristic_congr_codiscrete (eventuallyEq_out_toGerm hf) hr).symm

/-- The characteristic of a germ, evaluated through any representative. -/
theorem characteristic_eq_of_coe_eq {f : ℂ → ℂ} {a : germRing ℂ univ}
    (hfa : (f : Germ (codiscreteWithin (univ : Set ℂ)) ℂ)
      = (a : Germ (codiscreteWithin (univ : Set ℂ)) ℂ)) {r : ℝ} (hr : r ≠ 0) :
    characteristic a r = ValueDistribution.characteristic f ⊤ r :=
  (ValueDistribution.characteristic_congr_codiscrete (out_eventuallyEq hfa) hr).symm

theorem characteristic_nonneg (a : germRing ℂ univ) {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ characteristic a r :=
  ValueDistribution.characteristic_nonneg hr

theorem characteristic_zero {r : ℝ} (hr : r ≠ 0) : characteristic (0 : germRing ℂ univ) r = 0 := by
  rw [characteristic, ValueDistribution.characteristic_congr_codiscrete out_zero hr]
  simp

theorem characteristic_algebraMap (c : ℂ) {r : ℝ} (hr : r ≠ 0) :
    characteristic (algebraMap ℂ (germRing ℂ univ) c) r = log⁺ ‖c‖ := by
  rw [characteristic, ValueDistribution.characteristic_congr_codiscrete (out_algebraMap c) hr]
  simp

theorem characteristic_one {r : ℝ} (hr : r ≠ 0) : characteristic (1 : germRing ℂ univ) r = 0 := by
  simpa using characteristic_algebraMap 1 hr

theorem characteristic_add_le (a b : germRing ℂ univ) {r : ℝ} (hr : 1 ≤ r) :
    characteristic (a + b) r ≤ characteristic a r + characteristic b r + log 2 := by
  rw [characteristic, ValueDistribution.characteristic_congr_codiscrete (out_add a b)
    (zero_lt_one.trans_le hr).ne']
  exact ValueDistribution.characteristic_add_top_le (meromorphic_out a) (meromorphic_out b) hr

theorem characteristic_sum_le {ι : Type*} (s : Finset ι) (c : ι → germRing ℂ univ) {r : ℝ}
    (hr : 1 ≤ r) :
    characteristic (∑ i ∈ s, c i) r ≤ ∑ i ∈ s, characteristic (c i) r + log #s := by
  simp only [characteristic]
  rw [ValueDistribution.characteristic_congr_codiscrete (out_sum s c)
    (zero_lt_one.trans_le hr).ne']
  simpa [Finset.sum_apply] using
    ValueDistribution.characteristic_sum_top_le s (fun i ↦ out (c i))
      (fun i _ ↦ meromorphic_out (c i)) hr

theorem characteristic_mul_le (a b : germRing ℂ univ) {r : ℝ} (hr : 1 ≤ r) :
    characteristic (a * b) r ≤ characteristic a r + characteristic b r := by
  rw [characteristic, ValueDistribution.characteristic_congr_codiscrete (out_mul a b)
    (zero_lt_one.trans_le hr).ne']
  exact ValueDistribution.characteristic_mul_top_le' hr (meromorphic_out a) (meromorphic_out b)

theorem characteristic_pow (a : germRing ℂ univ) (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    characteristic (a ^ n) r = n * characteristic a r := by
  rw [characteristic, ValueDistribution.characteristic_congr_codiscrete (out_pow a n) hr,
    ValueDistribution.characteristic_pow_top (meromorphic_out a)]
  simp [characteristic]

theorem characteristic_neg (a : germRing ℂ univ) {r : ℝ} (hr : r ≠ 0) :
    characteristic (-a) r = characteristic a r := by
  rw [characteristic, ValueDistribution.characteristic_congr_codiscrete (out_neg a) hr]
  have : -out a = (-1 : ℂ) • out a := by ext z; simp
  rw [this]
  simp only [ValueDistribution.characteristic, Pi.add_apply]
  rw [ValueDistribution.logCounting_const_smul_top (by norm_num)]
  congr 1
  simp [ValueDistribution.proximity_top]

/-- The First Main Theorem for germs: the characteristics of `a` and `a⁻¹` differ by a
constant. (At `r = 0` the representatives `out a⁻¹` and `(out a)⁻¹` may differ, so the
constant also absorbs the value at `0`.) -/
theorem exists_abs_characteristic_inv_sub_le (a : germRing ℂ univ) :
    ∃ c, ∀ r, |characteristic a⁻¹ r - characteristic a r| ≤ c := by
  refine ⟨max (max |log ‖out a 0‖| |log ‖meromorphicTrailingCoeffAt (out a) 0‖|)
    |characteristic a⁻¹ 0 - characteristic a 0|, fun r ↦ ?_⟩
  by_cases hr : r = 0
  · subst hr
    exact le_max_right _ _
  refine le_max_of_le_left ?_
  rw [characteristic, ValueDistribution.characteristic_congr_codiscrete (out_inv a) hr,
    abs_sub_comm]
  exact ValueDistribution.characteristic_sub_characteristic_inv_le (meromorphic_out a)

/-!
## The Algebraic Dependence Bound for Germs
-/

/-- **The algebraic dependence bound for germs** (T2 at germ level): if
`a ^ d + Σ_{j<d} c j * a ^ j = 0` in the field of meromorphic germs, then
`T(r, a) ≤ Σ_{j<d} T(r, c j) + log d` for `1 ≤ r`. -/
theorem characteristic_le_sum_characteristic_of_monic_eq_zero {a : germRing ℂ univ}
    {c : ℕ → germRing ℂ univ} {d : ℕ} (h : a ^ d + ∑ j ∈ range d, c j * a ^ j = 0) {r : ℝ}
    (hr : 1 ≤ r) :
    characteristic a r ≤ ∑ j ∈ range d, characteristic (c j) r + log d := by
  -- The relation holds for the chosen representatives, away from a discrete set.
  have hrel : out a ^ d + ∑ j ∈ range d, out (c j) * out a ^ j =ᶠ[codiscrete ℂ] 0 := by
    have h₁ : out (a ^ d + ∑ j ∈ range d, c j * a ^ j)
        =ᶠ[codiscreteWithin univ] out a ^ d + ∑ j ∈ range d, out (c j) * out a ^ j :=
      (out_add _ _).trans ((out_pow a d).add ((out_sum _ _).trans
        (EventuallyEq.finset_sum fun j _ ↦ (out_mul _ _).trans
          ((EventuallyEq.refl _ _).mul (out_pow a j)))))
    rw [h] at h₁
    exact h₁.symm.trans out_zero
  exact ValueDistribution.characteristic_le_sum_characteristic_of_monic_eq_zero
    (meromorphic_out a) (fun j ↦ meromorphic_out (c j)) hrel hr

end MeromorphicOn.GermRing
