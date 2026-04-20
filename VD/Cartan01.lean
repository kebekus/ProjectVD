/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Stefan Kebekus
-/

module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction

public section

open Real
open scoped Real MeasureTheory Metric

/-!
# Cartan's Formula

The material in this file will, in the future, prove Cartan's formula, which
gives an integral presentation of the characteristic function of Value
Distribution Theory.

If `f : ℂ → ℂ` is meromorphic, then the value at `r` of the characteristic
function `characteristic f ⊤` equals the sum of the following two integrals.

- `circleAverage (logCounting f · r) 0 1` and

- `circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1`.

Cartan's formula implies the (surprisingly non-trivial) fact that the
characteristic function `characteristic f ⊤` is monotone.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic
Spaces*][MR886677] for a detailed discussion.

## Main Results

- `ValueDistribution.Cartan.circleIntegrable_circleAverage_log_norm_sub_unit`:
  Circle integrability of the first summand in Cartan's formula.

TODO:

- Finish proof of the Cartan's formula in full.

-/

/-!
## Generic material
-/



/-!
## Non-generic material: Cartan Kernel
-/


/-!
## Final
-/
namespace Cartan
/-- If `f` has a pole at the origin, then the Cartan trailing-coefficient correction term is circle
integrable in the value variable. -/
private lemma circleIntegrable_log_trailingCoeff_of_meromorphicOrderAt_neg {f : ℂ → ℂ}
    (h : MeromorphicOn f ⊤) (hneg : meromorphicOrderAt f 0 < 0) :
    CircleIntegrable
      (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  apply circleIntegrable_of_const_on_sphere (C := log ‖meromorphicTrailingCoeffAt f 0‖)
  exact log_trailingCoeff_eq_const_on_unitSphere_of_meromorphicOrderAt_neg h hneg

/-- If `f` has meromorphic order `0` at the origin, then the Cartan trailing-coefficient
correction term is circle integrable in the value variable. -/
private lemma circleIntegrable_log_trailingCoeff_of_meromorphicOrderAt_eq_zero {f : ℂ → ℂ}
    (h : MeromorphicOn f ⊤) (hzero : meromorphicOrderAt f 0 = 0) :
    CircleIntegrable
      (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  exact CircleIntegrable.congr_codiscreteWithin
    (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero h hzero)
    (circleIntegrable_log_norm_sub (meromorphicTrailingCoeffAt f 0) 0 1)

/-- If `f` has a zero at the origin, then the Cartan trailing-coefficient correction term is circle
integrable in the value variable. -/
private lemma circleIntegrable_log_trailingCoeff {f : ℂ → ℂ} (h : MeromorphicOn f ⊤)
    (h₂ : 0 < meromorphicOrderAt f 0) :
    CircleIntegrable
      (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  apply circleIntegrable_of_const_on_sphere (C := 0)
  exact log_trailingCoeff_eq_zero_on_unitSphere h h₂

/-- Auxiliary integrability statement for the trailing-coefficient term in Cartan's formula. -/
lemma circleIntegrable_log_trailingCoeff_of_meromorphic {f : ℂ → ℂ} (h : Meromorphic f) :
    CircleIntegrable
      (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  rcases lt_trichotomy (meromorphicOrderAt f 0) 0 with hneg | hzero | hpos
  · exact circleIntegrable_log_trailingCoeff_of_meromorphicOrderAt_neg h.meromorphicOn hneg
  · exact circleIntegrable_log_trailingCoeff_of_meromorphicOrderAt_eq_zero h.meromorphicOn hzero
  · exact circleIntegrable_log_trailingCoeff h.meromorphicOn hpos
end Cartan

namespace ValueDistribution


end ValueDistribution
