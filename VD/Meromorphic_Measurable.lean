import VD.MathlibPending.Nevanlinna_add_characteristic
import Mathlib.MeasureTheory.Integral.Prod

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {U : Set 𝕜}

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution

theorem MeromorphicOn.discreteTopology_not_analyticAt [CompleteSpace E] (h : MeromorphicOn f U) :
    IsDiscrete ({z | ¬AnalyticAt 𝕜 f z} ∩ U) := by
  apply isDiscrete_of_codiscreteWithin
  simp only [compl_setOf, Decidable.not_not]
  apply eventually_codiscreteWithin_analyticAt f h

theorem MeromorphicOn.countable_not_analyticAt [SecondCountableTopology 𝕜] [CompleteSpace E]
    (h : MeromorphicOn f U) :
    ({z | ¬AnalyticAt 𝕜 f z} ∩ U).Countable := by
  have : DiscreteTopology ↑({z | ¬AnalyticAt 𝕜 f z} ∩ U) := by
    sorry
  have := h.discreteTopology_not_analyticAt
  rw [isDiscrete_iff_discreteTopology] at this
  apply countable_of_Lindelof_of_discrete

lemma measurable_of_continuousOn_open_of_countable_closed {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (h_count : Uᶜ.Countable) (h_cont : ContinuousOn f U) : Measurable f := by
  -- Assume the contrary, that $f$ is not measurable.
  by_contra h_not_measurable;
  -- Since $f$ is not measurable, there exists an open set $V$ such that $f^{-1}(V)$ is not measurable.
  obtain ⟨V, hV_open, hV_not_meas⟩ : ∃ V : Set ℂ, IsOpen V ∧ ¬ MeasurableSet (f ⁻¹' V) := by
    -- By definition of measurability, if $f$ is not measurable, then there exists an open set $V$ such that $f^{-1}(V)$ is not measurable.
    have h_not_measurable_def : ¬(∀ V : Set ℂ, IsOpen V → MeasurableSet (f ⁻¹' V)) := by
      exact fun h => h_not_measurable <| measurable_of_isOpen h;
    aesop;
  -- Since $f$ is continuous on $U$, the preimage of any open set under $f|_U$ is open in $U$, hence measurable.
  have h_preimage_U_meas : MeasurableSet (f ⁻¹' V ∩ U) := by
    -- The preimage of an open set under a continuous function is open.
    have h_preimage_open : IsOpen (f ⁻¹' V ∩ U) := by
      rw [ isOpen_iff_mem_nhds ] at *
      intro x hx
      have left : f x ∈ V := by aesop
      have right : x ∈ U := by aesop
      exact h_cont.continuousAt ( hU x right ) |> fun h => h.tendsto.eventually ( hV_open _ left );
    exact h_preimage_open.measurableSet;
  -- Since $U^c$ is countable, the preimage $f^{-1}(V)$ can be written as the union of $f^{-1}(V) \cap U$ and $f^{-1}(V) \cap U^c$.
  have h_preimage_union : f ⁻¹' V = (f ⁻¹' V ∩ U) ∪ (f ⁻¹' V ∩ Uᶜ) := by
    rw [ ← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ ];
  -- Since $U^c$ is countable, the preimage $f^{-1}(V) \cap U^c$ is also countable.
  have h_preimage_Uc_countable : Set.Countable (f ⁻¹' V ∩ Uᶜ) := by
    exact h_count.mono fun x hx => hx.2;
  exact hV_not_meas <| h_preimage_union.symm ▸ MeasurableSet.union h_preimage_U_meas ( h_preimage_Uc_countable.measurableSet )


lemma meromorphic_measurable {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) :
    Measurable f := by

  -- The set of singularities of a meromorphic function is countable.
  have h_countable : Set.Countable {z : ℂ | ¬AnalyticAt ℂ f z} := by
    have := h.countable_not_analyticAt
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
