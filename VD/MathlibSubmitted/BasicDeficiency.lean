/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Truncated

/-!
# Deficiencies of Meromorphic Functions

Let `f` be meromorphic on the complex plane and let `a` be a value in `ℂ ∪ {∞}`, represented as an
element of `WithTop ℂ`. The characteristic function `characteristic f a` is the sum of two terms:
the proximity function `proximity f a`, which measures how close `f` comes to `a` on the circle of
radius `r`, and the logarithmic counting function `logCounting f a`, which counts the solutions of
`f = a` in the disk of radius `r`. By the First Main Theorem, `characteristic f a` agrees with
`characteristic f ⊤` up to a bounded function, so that the latter measures the growth of `f`
independently of `a`. The deficiency of `a` is the asymptotic share of the proximity function in
this growth. Values with positive deficiency are attained less often than the growth of `f` allows.

This file defines the deficiency and its truncated variant.

## Main definitions

- `ValueDistribution.deficiency`: the deficiency of `a`, the `liminf` as `r → ∞` of the quotient
  `proximity f a r / characteristic f ⊤ r`.
- `ValueDistribution.truncatedDeficiency`: the truncated deficiency of `a`, one minus the `limsup`
  as `r → ∞` of the quotient `truncatedLogCounting f a r / characteristic f ⊤ r`. The truncated
  logarithmic counting function counts the solutions of `f = a` without multiplicity.

## Main results

- `ValueDistribution.isBigO_truncatedLogCounting_characteristic_top`: if `f` is meromorphic and
  its characteristic function `characteristic f ⊤` tends to infinity, then the truncated logarithmic
  counting function is big-O of `characteristic f ⊤`.

## Implementation notes

The deficiencies are defined for every function `f : ℂ → E`, but they carry meaning only if the
characteristic function `characteristic f ⊤` tends to infinity. This is the case for every
meromorphic function that is not constant outside a discrete set.

For real-valued functions, the API for `Filter.liminf` and `Filter.limsup` requires boundedness
hypotheses (`Filter.IsBoundedUnder`, `Filter.IsCoboundedUnder`). For the quotients that define the
deficiencies, these hypotheses follow from
`ValueDistribution.isBigO_proximity_characteristic_top` and
`ValueDistribution.isBigO_truncatedLogCounting_characteristic_top`, using
`Asymptotics.div_isBoundedUnder_of_isBigO`.

See Section VII.3 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677], Section 2.5 of
[Hayman, *Meromorphic Functions*][MR164038] or Section 2.3 of [Noguchi-Winkelmann, *Nevanlinna
Theory in Several Complex Variables and Diophantine Approximation*][MR3156076] for a detailed
discussion.
-/

@[expose] public section

/-
# Upstreaming plan

Project context: this file is the first part of work package G (deficiencies and the defect
relation, S3) of the plan `VD/SMT/PLAN-SecondMainTheorem.md`, §9. It was split off from
`VD/SMT/Deficiency.lean` on 2026-11-27, together with the combined First Main Theorem from
`VD/SMT/SecondMainTheorem.lean`, and reworked for submission on the same day. Both files import
it. What remains in `VD/SMT/Deficiency.lean` is the basic API of the deficiencies, the bridges
providing `Tendsto (characteristic f ⊤) atTop atTop`, and the defect relation.

The rework replaced the helper lemmas of `VD/SMT/Deficiency.lean`, which were private proof
devices, by statements that make sense on their own:
- The combined First Main Theorem follows the pattern of `FirstMainTheorem.lean`: a quantitative
  version with an explicit constant, and a qualitative version in terms of `=O[atTop]`. The
  earlier form `∃ C, ∀ r, |characteristic f a r - characteristic f ⊤ r| ≤ C` is gone.
- The identity `characteristic f a₀ = characteristic (f · - a₀)⁻¹ ⊤` is split into the two
  identities it combines, `characteristic_coe_eq_characteristic_sub_const_zero` and
  `characteristic_inv`. They mirror the lemmas of the same names for `proximity` and
  `logCounting`.
- The bounds on the quotients are stated with `IsEquivalent` and `=O[atTop]`. Those that do not
  involve the truncated counting function are corollaries of the First Main Theorem and go to
  `FirstMainTheorem.lean` (Step 3). The earlier lemmas
  said that the three quotients eventually take values in `[0, 2]`, where the number `2` was
  arbitrary, and that their `limsup` is at most one. The latter statement was generic in the
  numerator and had nothing to do with Value Distribution Theory. It is not needed:
  `deficiency_le_one` and `truncatedDeficiency_nonneg` follow from
  `deficiency_eq_one_sub_limsup` and `deficiency_le_truncatedDeficiency`.
- Three statements that need no assumption on `f` are split off:
  `isBigO_proximity_characteristic`, `isBigO_logCounting_characteristic` and
  `isBigO_truncatedLogCounting_logCounting`.

Status: ready. The material depends on Mathlib master only. It was checked against the Mathlib
revision pinned in `lake-manifest.json` (`348837d3`, 2026-11-25): a copy of each target file with
the material of Steps 1–3 inserted compiles under Mathlib's linter set, and no target file needs a
new import. No open Mathlib PR treats deficiencies (search of 2026-11-27).

When to submit. Steps 1–3 extend existing files and make sense without Step 4. The new file of
Step 4 contains two definitions and one comparison statement, which is too little for a file of
its own. Recommendation: submit Steps 1–3 first, as a PR on the combined form of the First Main
Theorem, and let the new file follow together with the basic API. The basic API in
`VD/SMT/Deficiency.lean` (`deficiency_nonneg`, `deficiency_le_one`,
`truncatedDeficiency_nonneg`, `truncatedDeficiency_le_one`, `deficiency_eq_one_sub_limsup`,
`deficiency_le_truncatedDeficiency`, `deficiency_eq_one_of_logCounting_eq_zero`,
`tendsto_characteristic_atTop_of_log_isLittleO`) depends on Mathlib master only, too.

## Step 1: extend `Mathlib/Analysis/Complex/ValueDistribution/CharacteristicFunction.lean`

The four declarations of the section `CharacteristicFunction` of this file go to the end of the
section "Elementary Properties" of the target file, after `characteristic_eventually_nonneg`,
unchanged. The variables of the section agree with those of the target file. The target file
opens `Filter`, `Real` and `Set` only; this suffices, because the notation `=O[atTop]` is not
scoped.

Why this location: the two identities belong next to the definition, as their analogues
`proximity_coe_eq_proximity_sub_const_zero`, `proximity_inv`,
`logCounting_coe_eq_logCounting_sub_const_zero` and `logCounting_inv` do. The two big-O statements
need nothing but the nonnegativity of the two summands of the characteristic function.

## Step 2: extend `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean`

The declaration of the section `Truncated` of this file goes into the target file, after
`truncatedLogCounting_nonneg`, unchanged. The variables of the section are among those of the
target file.

## Step 3: extend `Mathlib/Analysis/Complex/ValueDistribution/FirstMainTheorem.lean`

The section `CombinedForm` of this file, with the heading that precedes it, goes into the target
file, between `end SecondPart` and `section moebius`, unchanged. Besides the two versions of the
combined form, the section contains its consequences for functions whose characteristic function
tends to infinity: `isEquivalent_characteristic_characteristic_top`,
`isBigO_proximity_characteristic_top` and `isBigO_logCounting_characteristic_top`. The target file
opens `Asymptotics` already, as the notation `~[atTop]` requires.

The module docstring of the target file gains a third item, after the two items on the two parts:

    - If `f` is meromorphic on the complex plane, then for every value `a`, the characteristic
      functions `characteristic f ⊤` and `characteristic f a` agree up to a constant. This
      combines the two parts. If `characteristic f ⊤` tends to infinity, the two functions are
      asymptotically equivalent.

Why this location: the combined form is a direct corollary of the two parts of the First Main
Theorem, and the form in which the theorem is usually applied. The Second Main Theorem will use
the quantitative version. The three consequences say nothing about deficiencies, and this is the
first file where they can be stated.

## Step 4: new file `Mathlib/Analysis/Complex/ValueDistribution/Deficiency/Basic.lean`

The new file is this file without the three sections of Steps 1–3 and without this comment. The
module docstring and the imports stay. The line `open Asymptotics Filter Real` becomes
`open Filter`, because the section `CombinedForm` is the only one that needs the other two.
Add the file to `Mathlib.lean`.

Why this location: it follows the layout of `LogCounting/Basic.lean` and `Proximity/Basic.lean`.
The basic API and the defect relation of `VD/SMT/Deficiency.lean` can later go to further files in
the directory `Deficiency/`, or into this file.

## PR title and description (draft)

The paragraphs are wrapped to fit this file. Join the lines of each paragraph before pasting,
because GitHub renders line breaks in PR descriptions.

Title:

    feat(Analysis/Complex/ValueDistribution): deficiencies of meromorphic functions

Description:

    Define the deficiency and the truncated deficiency of a value `a ∈ ℂ ∪ {∞}` of a meromorphic
    function `f` on the complex plane. The deficiency is the `liminf` as `r → ∞` of
    `proximity f a r / characteristic f ⊤ r`; the truncated deficiency is one minus the `limsup`
    of `truncatedLogCounting f a r / characteristic f ⊤ r`. Here `proximity`,
    `truncatedLogCounting` and `characteristic` are the proximity function, the truncated
    logarithmic counting function and the characteristic function of Value Distribution Theory.
    Values with positive deficiency are attained less often than the growth of the function
    allows.

    Establish the combined form of the First Main Theorem: for every value `a`, the
    characteristic functions `characteristic f a` and `characteristic f ⊤` differ by a bounded
    function. Deduce that, if `characteristic f ⊤` tends to infinity, then `characteristic f a`
    is asymptotically equivalent to it, and the proximity function, the logarithmic counting
    function and the truncated logarithmic counting function are big-O of it. These statements
    provide the boundedness hypotheses of the `liminf`/`limsup` API, as needed for the basic
    properties of the deficiencies and for the defect relation, which bounds the sum of the
    truncated deficiencies over any finite set of values by two.

    The PR will be used in [Project VD](https://github.com/kebekus/ProjectVD), formalizing Value
    Distribution Theory for meromorphic functions on the complex plane, in order to establish
    the defect relation of Value Distribution Theory. Claude Code was used to create this PR.

## Step 5: after the merge

- Delete this file and remove `VD.SMT.Deficiency.Basic` from `VD.lean`.
- In `VD/SMT/Deficiency.lean`, replace the import of this file by
  `Mathlib.Analysis.Complex.ValueDistribution.Deficiency.Basic`.
- In `VD/SMT/SecondMainTheorem.lean`, remove the import of this file; the First Main Theorem
  reaches it through its other imports.
- `VD/MathlibPending/BoundednessCharacteristic.lean`: the forward direction of
  `characteristic_isBigO_iff` is `isBigO_proximity_characteristic.trans` together with
  `isBigO_logCounting_characteristic.trans`.
- Update §9 and item 7 of the PR list in §11 of `VD/SMT/PLAN-SecondMainTheorem.md`.

## Where the material ends up

| Declaration                                           | Mathlib target                 |
| ----------------------------------------------------- | ------------------------------ |
| `characteristic_coe_eq_characteristic_sub_const_zero` | `CharacteristicFunction.lean`  |
| `characteristic_inv`                                  | `CharacteristicFunction.lean`  |
| `isBigO_proximity_characteristic`                     | `CharacteristicFunction.lean`  |
| `isBigO_logCounting_characteristic`                   | `CharacteristicFunction.lean`  |
| `isBigO_truncatedLogCounting_logCounting`             | `LogCounting/Truncated.lean`   |
| `abs_characteristic_top_sub_characteristic_coe_le`    | `FirstMainTheorem.lean`        |
| `isBigO_characteristic_top_sub_characteristic`        | `FirstMainTheorem.lean`        |
| `deficiency`                                          | `Deficiency/Basic.lean`        |
| `truncatedDeficiency`                                 | `Deficiency/Basic.lean`        |
| `isEquivalent_characteristic_characteristic_top`      | `FirstMainTheorem.lean`        |
| `isBigO_proximity_characteristic_top`                 | `FirstMainTheorem.lean`        |
| `isBigO_logCounting_characteristic_top`               | `FirstMainTheorem.lean`        |
| `isBigO_truncatedLogCounting_characteristic_top`      | `Deficiency/Basic.lean`        |
-/

open Asymptotics Filter Real

namespace ValueDistribution

section CharacteristicFunction

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {a : WithTop E}

/--
For finite values `a₀`, the characteristic function `characteristic f a₀` equals the characteristic
function for the value zero of the shifted function `f - a₀`.
-/
lemma characteristic_coe_eq_characteristic_sub_const_zero {a₀ : E} :
    characteristic f a₀ = characteristic (f - fun _ ↦ a₀) 0 := by
  rw [characteristic, characteristic, proximity_coe_eq_proximity_sub_const_zero,
    logCounting_coe_eq_logCounting_sub_const_zero]

/--
For complex-valued `f`, the characteristic function of `f⁻¹` for the value `⊤` equals the
characteristic function of `f` for the value zero.
-/
theorem characteristic_inv {f : ℂ → ℂ} : characteristic f⁻¹ ⊤ = characteristic f 0 := by
  rw [characteristic, characteristic, proximity_inv, logCounting_inv]

/--
The proximity function `proximity f a` is big-O of the characteristic function `characteristic f a`:
it is one of the two summands of the characteristic function, and the other summand is
asymptotically non-negative.
-/
theorem isBigO_proximity_characteristic : proximity f a =O[atTop] characteristic f a := by
  refine .of_norm_eventuallyLE ?_
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [norm_of_nonneg (proximity_nonneg r)]
  exact le_add_of_nonneg_right (logCounting_nonneg hr)

/--
The logarithmic counting function `logCounting f a` is big-O of the characteristic function
`characteristic f a`: it is asymptotically non-negative, and the other summand of the characteristic
function is non-negative.
-/
theorem isBigO_logCounting_characteristic : logCounting f a =O[atTop] characteristic f a := by
  refine .of_norm_eventuallyLE ?_
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [norm_of_nonneg (logCounting_nonneg hr)]
  exact le_add_of_nonneg_left (proximity_nonneg r)

end CharacteristicFunction

section Truncated

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {a : WithTop E}

/--
The truncated logarithmic counting function is big-O of the ordinary logarithmic counting function.
-/
theorem isBigO_truncatedLogCounting_logCounting :
    truncatedLogCounting f a =O[atTop] logCounting f a := by
  refine .of_norm_eventuallyLE ?_
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [norm_of_nonneg (truncatedLogCounting_nonneg hr)]
  exact truncatedLogCounting_le hr

end Truncated

/-!
## Combined Form of the First Main Theorem

The two parts of the First Main Theorem combine to the statement that the characteristic functions
of `f` for the value `⊤` and for any other value agree up to a bounded function. If the
characteristic function tends to infinity, the bounded error is negligible.
-/

section CombinedForm

variable {f : ℂ → ℂ} {a₀ : ℂ} {a : WithTop ℂ}

/--
First Main Theorem of Value Distribution Theory, combined form, quantitative version: If `f` is
meromorphic on the complex plane, then the characteristic functions of `f` for the value `⊤` and
for a finite value `a₀` differ at most by an explicit constant. The constant is the sum of the
constants of the two parts of the First Main Theorem: the second part compares `f` with the shifted
function `f - a₀`, and the first part compares `f - a₀` with its inverse.
-/
theorem abs_characteristic_top_sub_characteristic_coe_le {r : ℝ} (hf : Meromorphic f) :
    |characteristic f ⊤ r - characteristic f a₀ r|
      ≤ log⁺ ‖a₀‖ + log 2
        + max |log ‖f 0 - a₀‖| |log ‖meromorphicTrailingCoeffAt (f · - a₀) 0‖| := by
  rw [characteristic_coe_eq_characteristic_sub_const_zero, ← characteristic_inv]
  exact (abs_sub_le _ (characteristic (f · - a₀) ⊤ r) _).trans <|
    add_le_add (abs_characteristic_sub_characteristic_shift_le hf)
      (characteristic_sub_characteristic_inv_le (by fun_prop))

/--
First Main Theorem of Value Distribution Theory, combined form, qualitative version: If `f` is
meromorphic on the complex plane, then for every value `a`, the characteristic functions of `f` for
the values `⊤` and `a` agree asymptotically up to a bounded function. See
`ValueDistribution.abs_characteristic_top_sub_characteristic_coe_le` for an explicit bound.
-/
theorem isBigO_characteristic_top_sub_characteristic (hf : Meromorphic f) :
    (characteristic f ⊤ - characteristic f a) =O[atTop] (1 : ℝ → ℝ) := by
  cases a with
  | top => exact isBigO_of_le' (c := 0) _ fun r ↦ by simp
  | coe a₀ =>
    exact isBigO_of_le' _ fun r ↦ by
      simpa using abs_characteristic_top_sub_characteristic_coe_le hf

/--
First Main Theorem of Value Distribution Theory, asymptotic version: If `f` is meromorphic on the
complex plane and its characteristic function tends to infinity, then for every value `a`, the
characteristic function `characteristic f a` is asymptotically equivalent to `characteristic f ⊤`.
See `ValueDistribution.isBigO_characteristic_top_sub_characteristic` for the underlying statement,
which holds without the assumption on the characteristic function.
-/
theorem isEquivalent_characteristic_characteristic_top (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) :
    characteristic f a ~[atTop] characteristic f ⊤ :=
  ((isBigO_characteristic_top_sub_characteristic hf).trans_isLittleO <|
    (isLittleO_one_left_iff ℝ).2 <| tendsto_norm_atTop_atTop.comp hT).symm

/--
If `f` is meromorphic on the complex plane and its characteristic function tends to infinity, then
the proximity function `proximity f a` is big-O of `characteristic f ⊤`.
-/
theorem isBigO_proximity_characteristic_top (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) :
    proximity f a =O[atTop] characteristic f ⊤ :=
  isBigO_proximity_characteristic.trans
    (isEquivalent_characteristic_characteristic_top hf hT).isBigO

/--
If `f` is meromorphic on the complex plane and its characteristic function tends to infinity, then
the logarithmic counting function `logCounting f a` is big-O of `characteristic f ⊤`.
-/
theorem isBigO_logCounting_characteristic_top (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) :
    logCounting f a =O[atTop] characteristic f ⊤ :=
  isBigO_logCounting_characteristic.trans
    (isEquivalent_characteristic_characteristic_top hf hT).isBigO

end CombinedForm

/-!
## Definition of the Deficiencies
-/

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/--
The **deficiency** of a value `a`: the asymptotic proportion of the characteristic function that
stems from the proximity function, i.e. from radii `r` where `f` is close to `a` on a large
portion of the circle `‖z‖ = r`. Values with positive deficiency are attained less often than the
First Main Theorem allows.
-/
noncomputable def deficiency (f : ℂ → E) (a : WithTop E) : ℝ :=
  liminf (fun r ↦ proximity f a r / characteristic f ⊤ r) atTop

/--
The **truncated deficiency** of a value `a`, defined through the truncated logarithmic counting
function `truncatedLogCounting f a`, which counts the solutions of `f = a` without multiplicity. It
measures both the deficiency of `a` and the asymptotic amount of ramification of `f` over `a`. For
meromorphic functions with unbounded characteristic function, the truncated deficiency dominates
the deficiency.
-/
noncomputable def truncatedDeficiency (f : ℂ → E) (a : WithTop E) : ℝ :=
  1 - limsup (fun r ↦ truncatedLogCounting f a r / characteristic f ⊤ r) atTop

end Definitions

/-!
## Comparison with the Characteristic Function

If the characteristic function `characteristic f ⊤` of a meromorphic function `f` tends to infinity,
then the functions that enter the definitions of the deficiencies are big-O of it. For the proximity
function, this is `ValueDistribution.isBigO_proximity_characteristic_top`.
-/

variable {f : ℂ → ℂ} {a : WithTop ℂ}

/--
If `f` is meromorphic on the complex plane and its characteristic function tends to infinity, then
the truncated logarithmic counting function `truncatedLogCounting f a` is big-O of
`characteristic f ⊤`.
-/
theorem isBigO_truncatedLogCounting_characteristic_top (hf : Meromorphic f)
    (hT : Tendsto (characteristic f ⊤) atTop atTop) :
    truncatedLogCounting f a =O[atTop] characteristic f ⊤ :=
  isBigO_truncatedLogCounting_logCounting.trans (isBigO_logCounting_characteristic_top hf hT)

end ValueDistribution
