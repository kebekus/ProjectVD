import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Filter Set Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {U : Set 𝕜}

/--
The singular set of a meromorphic function is countable.
-/
theorem MeromorphicOn.countable_compl_analyticAt [SecondCountableTopology 𝕜] [CompleteSpace E]
    (h : MeromorphicOn f U) :
    ({z | AnalyticAt 𝕜 f z}ᶜ ∩ U).Countable := by
  classical
  have : DiscreteTopology ↑({z | AnalyticAt 𝕜 f z}ᶜ ∩ U) := by
    apply isDiscrete_iff_discreteTopology.1 (isDiscrete_of_codiscreteWithin _)
    simpa using eventually_codiscreteWithin_analyticAt f h
  apply countable_of_Lindelof_of_discrete


variable
  [MeasurableSpace 𝕜] [SecondCountableTopology 𝕜] [BorelSpace 𝕜]
  [MeasurableSpace E] [CompleteSpace E] [BorelSpace E]

/--
Meromorphic functions are measurable.
-/
theorem meromorphic_measurable {f : 𝕜 → E} (h : MeromorphicOn f Set.univ) :
    Measurable f := by
  set s := {z : 𝕜 | AnalyticAt 𝕜 f z}
  have h₁ : sᶜ.Countable  := by simpa using h.countable_compl_analyticAt
  have h₂ : IsOpen s := isOpen_analyticAt 𝕜 f
  have h₃ : ContinuousOn f s := fun z hz ↦ hz.continuousAt.continuousWithinAt
  apply measurable_of_isOpen
  intro V hV
  rw [(by aesop : f ⁻¹' V = (f ⁻¹' V ∩ s) ∪ (f ⁻¹' V ∩ sᶜ))]
  apply MeasurableSet.union (IsOpen.measurableSet _) (h₁.mono inter_subset_right).measurableSet
  rw [isOpen_iff_mem_nhds] at *
  intro x a
  simp_all [mem_setOf_eq, mem_inter_iff, mem_preimage, inter_mem_iff, and_true, s]
  apply h₃.continuousAt (h₂ x a.2) (hV (f x) a.1)
