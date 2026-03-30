/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
--module

import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.IsolatedZeros

open Complex ComplexConjugate Filter Function Metric Set Topology Real

set_option backward.isDefEq.respectTransparency false


/-!
## Material starts here
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {x : 𝕜} {f g : 𝕜 → E}

/-
If two meromorphic functions agree outside a set codiscrete within a perfect
set, then they agree in punctured neighbourhoods of every point in the perfect
set.
-/
theorem MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x)
    (hx : x ∈ U)
    (hU : Preperfect U)
    (h : f =ᶠ[Filter.codiscreteWithin U] g) :
    f =ᶠ[𝓝[≠] x] g :=
  hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hg hx (hU x hx) h

/-
If two meromorphic functions agree outside a set codiscrete within a perfect
set, then they define the same divisors there.
-/
theorem MeromorphicOn.divisor_of_eventuallyEq_codiscreteWithin_preperfect
    (hf : MeromorphicOn f U)
    (hg : MeromorphicOn g U)
    (hU : Preperfect U)
    (h : f =ᶠ[Filter.codiscreteWithin U] g) :
    divisor f U = divisor g U := by
  ext z
  by_cases hz : z ∉ U
  · simp_all
  rw [not_not] at hz
  rw [divisor_apply hf hz, divisor_apply hg hz]
  congr 1
  apply meromorphicOrderAt_congr
  apply (hf z hz).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect (hg z hz) hz hU h

/-
Open subsects in perfect spaces are preperfect.
-/
theorem PerfectSpace.preperfect_of_isOpen {α : Type*} [TopologicalSpace α] [PerfectSpace α] {U : Set α} (hU : IsOpen U) :
    Preperfect U := by
  rw [← inter_univ (a := U)]
  exact Preperfect.open_inter univ_preperfect hU

/-
Closures of open subsects in perfect spaces are preperfect, hence perfect.
-/
theorem PerfectSpace.preperfect_closure_of_isOpen {α : Type*} [TopologicalSpace α] [PerfectSpace α] {U : Set α} (hU : IsOpen U) :
    Preperfect (closure U) :=
  (PerfectSpace.preperfect_of_isOpen hU).perfect_closure.2
