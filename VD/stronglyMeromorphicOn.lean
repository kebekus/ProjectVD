import Mathlib.Algebra.BigOperators.Finprod
import VD.stronglyMeromorphicAt

open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem MeromorphicOn.analyticAt_codiscreteWithin [CompleteSpace E]
  {f : 𝕜 → E}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  { x | AnalyticAt 𝕜 f x } ∈ Filter.codiscreteWithin U := by
  rw [mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right, ← Filter.eventually_mem_set]
  apply (hf x hx).eventually_analyticAt.mono
  simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_setOf_eq, not_and, not_not]
  tauto

theorem MeromorphicOn.meromorphicNFAt_codiscreteWithin [CompleteSpace E]
    {f : 𝕜 → E} {U : Set 𝕜} (hf : MeromorphicOn f U) :
    { x | MeromorphicNFAt f x } ∈ Filter.codiscreteWithin U := by
  filter_upwards [hf.analyticAt_codiscreteWithin] with _ ha
  exact ha.MeromorphicNFAt

/- Strongly MeromorphicOn -/
def StronglyMeromorphicOn
  (f : 𝕜 → E)
  (U : Set 𝕜) :=
  ∀ z ∈ U, MeromorphicNFAt f z

/- Strongly MeromorphicAt is Meromorphic -/
theorem StronglyMeromorphicOn.meromorphicOn
  {f : 𝕜 → E}
  {U : Set 𝕜}
  (hf : StronglyMeromorphicOn f U) :
  MeromorphicOn f U := fun z hz ↦ (hf z hz).meromorphicAt

/- Strongly MeromorphicOn of non-negative order is analytic -/
theorem StronglyMeromorphicOn.analytic
  {f : 𝕜 → E}
  {U : Set 𝕜}
  (h₁f : StronglyMeromorphicOn f U)
  (h₂f : ∀ x, (hx : x ∈ U) → 0 ≤ (h₁f x hx).meromorphicAt.order) :
  AnalyticOnNhd 𝕜 f U := fun z hz ↦ (h₁f z hz).analyticAt (h₂f z hz)

/- Analytic functions are strongly meromorphic -/
theorem AnalyticOn.stronglyMeromorphicOn
  {f : 𝕜 → E}
  {U : Set 𝕜}
  (h₁f : AnalyticOnNhd 𝕜 f U) :
  StronglyMeromorphicOn f U :=
  fun z hz ↦ (h₁f z hz).MeromorphicNFAt

theorem stronglyMeromorphicOn_of_mul_analytic'
  {f : 𝕜 → E}
  {g : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁g : AnalyticOnNhd 𝕜 g U)
  (h₂g : ∀ u : U, g u ≠ 0)
  (h₁f : StronglyMeromorphicOn f U) :
  StronglyMeromorphicOn (g • f) U := by
  intro z hz
  apply (MeromorphicNFAt_of_mul_analytic (h₁g z hz) ?h₂g).mp (h₁f z hz)
  exact h₂g ⟨z, hz⟩

/- Make strongly MeromorphicOn -/
noncomputable def MeromorphicOn.makeStronglyMeromorphicOn
  {f : 𝕜 → E}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  𝕜 → E := by
  intro z
  by_cases hz : z ∈ U
  · exact (hf z hz).toNF z
  · exact f z

theorem makeStronglyMeromorphicOn_changeDiscrete [CompleteSpace E]
  {f : 𝕜 → E}
  {U : Set 𝕜}
  {z₀ : 𝕜}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  hf.makeStronglyMeromorphicOn =ᶠ[𝓝[≠] z₀] f := by
  apply Filter.eventually_iff_exists_mem.2
  obtain ⟨V, h₁V, h₂V⟩ := Filter.eventually_iff_exists_mem.1 (hf z₀ hz₀).eventually_analyticAt
  use V, h₁V
  intro v hv
  unfold MeromorphicOn.makeStronglyMeromorphicOn
  by_cases h₂v : v ∈ U
  · simp [h₂v]
    rw [← MeromorphicNFAt.toNF_eq_id]
    exact AnalyticAt.MeromorphicNFAt (h₂V v hv)
  · simp [h₂v]

theorem makeStronglyMeromorphicOn_changeDiscrete' [CompleteSpace E]
  {f : 𝕜 → E}
  {U : Set 𝕜}
  {z₀ : 𝕜}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  hf.makeStronglyMeromorphicOn =ᶠ[𝓝 z₀] (hf z₀ hz₀).toNF := by
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  · apply Filter.EventuallyEq.trans (makeStronglyMeromorphicOn_changeDiscrete hf hz₀)
    exact MeromorphicAt.toNF_id_on_nhdNE (hf z₀ hz₀)
  · rw [MeromorphicOn.makeStronglyMeromorphicOn]
    simp [hz₀]

theorem makeStronglyMeromorphicOn_changeDiscrete'' [CompleteSpace E]
  {f : 𝕜 → E}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  f =ᶠ[Filter.codiscreteWithin U] hf.makeStronglyMeromorphicOn := by
  filter_upwards [hf.meromorphicNFAt_codiscreteWithin] with x hx
  rw [MeromorphicOn.makeStronglyMeromorphicOn]
  by_cases h₁x : x ∈ U <;> simp [h₁x]
  · rw [← MeromorphicNFAt.toNF_eq_id hx]

theorem stronglyMeromorphicOn_of_makeStronglyMeromorphicOn [CompleteSpace E]
  {f : 𝕜 → E}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  StronglyMeromorphicOn hf.makeStronglyMeromorphicOn U := by
  intro z hz
  let A := makeStronglyMeromorphicOn_changeDiscrete' hf hz
  rw [meromorphicNFAt_congr A]
  exact (hf z hz).MeromorphicNFAt_of_toNF

theorem makeStronglyMeromorphicOn_changeOrder [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z₀ : 𝕜}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  (stronglyMeromorphicOn_of_makeStronglyMeromorphicOn hf z₀ hz₀).meromorphicAt.order = (hf z₀ hz₀).order := by
  apply MeromorphicAt.order_congr
  exact makeStronglyMeromorphicOn_changeDiscrete hf hz₀
