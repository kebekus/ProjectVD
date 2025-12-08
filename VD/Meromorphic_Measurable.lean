import VD.MathlibPending.Nevanlinna_add_characteristic
import Mathlib.MeasureTheory.Integral.Prod

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {U : Set 𝕜}

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution

theorem MeromorphicOn.discreteTopology_compl_analyticAt [CompleteSpace E] (h : MeromorphicOn f U) :
    IsDiscrete ({z | ¬AnalyticAt 𝕜 f z} ∩ U) := by
  apply isDiscrete_of_codiscreteWithin
  simp only [compl_setOf, Decidable.not_not]
  apply eventually_codiscreteWithin_analyticAt f h

theorem MeromorphicOn.countable_compl_analyticAt [SecondCountableTopology 𝕜] [CompleteSpace E]
    (h : MeromorphicOn f U) :
    ({z | ¬AnalyticAt 𝕜 f z} ∩ U).Countable := by
  have := isDiscrete_iff_discreteTopology.1 h.discreteTopology_compl_analyticAt
  apply countable_of_Lindelof_of_discrete

lemma measurable_of_continuousOn_open_of_countable_closed {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (h_count : Uᶜ.Countable) (h_cont : ContinuousOn f U) : Measurable f := by
  apply measurable_of_isOpen
  intro V hV
  have h_preimage_union : f ⁻¹' V = (f ⁻¹' V ∩ U) ∪ (f ⁻¹' V ∩ Uᶜ) := by
    aesop
  rw [h_preimage_union]
  apply MeasurableSet.union _ (h_count.mono inter_subset_right).measurableSet
  apply IsOpen.measurableSet
  rw [isOpen_iff_mem_nhds ] at *
  intro x a
  simp_all
  apply h_cont.continuousAt (hU x a.2) (hV (f x) a.1)


lemma meromorphic_measurable {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) :
    Measurable f := by

  -- The set of singularities of a meromorphic function is countable.
  have h_countable : Set.Countable {z : ℂ | ¬AnalyticAt ℂ f z} := by
    have := h.countable_compl_analyticAt
    simp_all

  -- Since $U$ is open and $f$ is continuous on $U$, and the complement of $U$ is countable, we can apply the lemma to conclude that $f$ is measurable.
  have hU : IsOpen {z : ℂ | AnalyticAt ℂ f z} := by
    exact isOpen_analyticAt ℂ f
  have h_cont : ContinuousOn f {z : ℂ | AnalyticAt ℂ f z} := by
    exact fun x hx => hx.continuousAt.continuousWithinAt
  have h_count : {z : ℂ | ¬AnalyticAt ℂ f z}.Countable := by
    -- Apply the fact that the set of points where f is not analytic is countable.
    exact h_countable
  exact measurable_of_continuousOn_open_of_countable_closed hU h_count h_cont
