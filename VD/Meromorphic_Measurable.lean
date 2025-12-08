import VD.MathlibPending.Nevanlinna_add_characteristic
import Mathlib.MeasureTheory.Integral.Prod

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {U : Set 𝕜}

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution

/--
The singular set of a meromorphic function is countable.
-/
theorem MeromorphicOn.countable_compl_analyticAt [SecondCountableTopology 𝕜] [CompleteSpace E]
    (h : MeromorphicOn f U) :
    ({z | AnalyticAt 𝕜 f z}ᶜ ∩ U).Countable := by
  have : DiscreteTopology ↑({z | AnalyticAt 𝕜 f z}ᶜ ∩ U) := by
    apply isDiscrete_iff_discreteTopology.1
    apply isDiscrete_of_codiscreteWithin
    simp only [compl_setOf, Decidable.not_not]
    apply eventually_codiscreteWithin_analyticAt f h
  apply countable_of_Lindelof_of_discrete

/--
Meromorphic functions of complex numbers are measurable.
-/
theorem meromorphic_measurable {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) :
    Measurable f := by
  have h₁ : Set.Countable {z : ℂ | AnalyticAt ℂ f z}ᶜ := by
    simpa using h.countable_compl_analyticAt
  have h₂ : IsOpen {z : ℂ | AnalyticAt ℂ f z} :=
    isOpen_analyticAt ℂ f
  have h₃ : ContinuousOn f {z : ℂ | AnalyticAt ℂ f z} :=
    fun x hx ↦ hx.continuousAt.continuousWithinAt
  apply measurable_of_isOpen
  intro V hV
  rw [(by aesop : f ⁻¹' V = (f ⁻¹' V ∩ {z : ℂ | AnalyticAt ℂ f z}) ∪
    (f ⁻¹' V ∩ {z : ℂ | AnalyticAt ℂ f z}ᶜ))]
  apply MeasurableSet.union (IsOpen.measurableSet _) (h₁.mono inter_subset_right).measurableSet
  rw [isOpen_iff_mem_nhds] at *
  intro x a
  simp_all only [top_eq_univ, mem_setOf_eq, mem_inter_iff, mem_preimage, inter_mem_iff, and_true]
  apply h₃.continuousAt (h₂ x a.2) (hV (f x) a.1)
