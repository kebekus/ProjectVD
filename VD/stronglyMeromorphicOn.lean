import Mathlib.Algebra.BigOperators.Finprod
import VD.stronglyMeromorphicAt

open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]


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
  AnalyticOnNhd 𝕜 f U := fun z hz ↦ (h₁f z hz).order_nonneg_iff_analyticAt.1 (h₂f z hz)

/- Analytic functions are strongly meromorphic -/
theorem AnalyticOn.stronglyMeromorphicOn
  {f : 𝕜 → E}
  {U : Set 𝕜}
  (h₁f : AnalyticOnNhd 𝕜 f U) :
  StronglyMeromorphicOn f U :=
  fun z hz ↦ (h₁f z hz).meromorphicNFAt

theorem stronglyMeromorphicOn_of_mul_analytic'
  {f : 𝕜 → E}
  {g : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁g : AnalyticOnNhd 𝕜 g U)
  (h₂g : ∀ u : U, g u ≠ 0)
  (h₁f : StronglyMeromorphicOn f U) :
  StronglyMeromorphicOn (g • f) U := by
  intro z hz
  apply MeromorphicNFAt.meromorphicNFAt_of_smul_analytic (h₁f z hz) (h₁g z hz)
  exact h₂g ⟨z, hz⟩

/- Make strongly MeromorphicOn -/
noncomputable def makeStronglyMeromorphicOn
  (f : 𝕜 → 𝕜) (U : Set 𝕜) :
  𝕜 → 𝕜 := by
  intro z
  by_cases hz : z ∈ U
  · exact toMeromorphicNFAt f z z
  · exact f z

theorem makeStronglyMeromorphicOn_changeDiscrete [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z₀ : 𝕜}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  makeStronglyMeromorphicOn f U =ᶠ[𝓝[≠] z₀] f := by
  apply Filter.eventually_iff_exists_mem.2
  let A := (hf z₀ hz₀).eventually_analyticAt
  obtain ⟨V, h₁V, h₂V⟩  := Filter.eventually_iff_exists_mem.1 A
  use V
  constructor
  · assumption
  · intro v hv
    unfold makeStronglyMeromorphicOn
    by_cases h₂v : v ∈ U
    · simp [h₂v]
      let B := (h₂V v hv).meromorphicNFAt
      let Z := toMeromorphicNFAt_eq_self.1 B
      rw [eq_comm]
      rw [← Z]
    · simp [h₂v]

theorem makeStronglyMeromorphicOn_changeDiscrete' [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z₀ : 𝕜}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  makeStronglyMeromorphicOn f U =ᶠ[𝓝 z₀] toMeromorphicNFAt f z₀ := by
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  · apply Filter.EventuallyEq.trans (makeStronglyMeromorphicOn_changeDiscrete hf hz₀)
    exact MeromorphicAt.eq_nhdNE_toMeromorphicNFAt (hf z₀ hz₀)
  · rw [makeStronglyMeromorphicOn]
    simp [hz₀]

theorem makeStronglyMeromorphicOn_changeDiscrete'' [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  f =ᶠ[Filter.codiscreteWithin U] makeStronglyMeromorphicOn f U := by

  rw [Filter.eventuallyEq_iff_exists_mem]
  use { x | AnalyticAt 𝕜 f x }, hf.analyticAt_codiscreteWithin
  intro x hx
  simp at hx
  rw [makeStronglyMeromorphicOn]
  by_cases h₁x : x ∈ U
  · simp [h₁x]
    rw [← toMeromorphicNFAt_eq_self.1 hx.meromorphicNFAt]
  · simp [h₁x]

theorem stronglyMeromorphicOn_of_makeStronglyMeromorphicOn [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  StronglyMeromorphicOn (makeStronglyMeromorphicOn f U) U := by
  intro z hz
  let A := makeStronglyMeromorphicOn_changeDiscrete' hf hz
  rw [meromorphicNFAt_congr A]
  exact meromorphicNFAt_toMeromorphicNFAt

theorem makeStronglyMeromorphicOn_changeOrder [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z₀ : 𝕜}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  (stronglyMeromorphicOn_of_makeStronglyMeromorphicOn hf z₀ hz₀).meromorphicAt.order = (hf z₀ hz₀).order := by
  apply MeromorphicAt.order_congr
  exact makeStronglyMeromorphicOn_changeDiscrete hf hz₀

theorem StronglyMeromorphicOn.order_ne_top
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁f : StronglyMeromorphicOn f U)
  (hU : IsConnected U)
  (h₂f : ∃ u : U, f u ≠ 0) :
  ∀ u : U, (h₁f u u.2).meromorphicAt.order ≠ ⊤ := by

  rw [← h₁f.meromorphicOn.exists_order_ne_top_iff_forall hU]
  obtain ⟨u, hu⟩ := h₂f
  use u
  rw [← (h₁f u u.2).order_eq_zero_iff] at hu
  rw [hu]
  simp
