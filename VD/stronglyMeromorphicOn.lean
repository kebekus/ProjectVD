import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Meromorphic.Divisor.MeromorphicFunction
import VD.ToMathlib.MeromorphicNFAt
import VD.meromorphicAt

open Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E}
  {x : 𝕜}
  {U : Set 𝕜}

/-!
# Normal form of meromorphic functions on a given set

## Definition
-/

/-- A function is 'meromorphic in normal form' on `U` if has normal form at
every point of `U`. -/
def MeromorphicNFOn (f : 𝕜 → E) (U : Set 𝕜) := ∀ z ∈ U, MeromorphicNFAt f z

/-!
## Relation to other properties of functions
-/

/-- If a function is meromorphic in normal form on `U`, then it is meromorphic on `U`. -/
theorem MeromorphicNFOn.meromorphicOn (hf : MeromorphicNFOn f U) :
    MeromorphicOn f U := fun z hz ↦ (hf z hz).meromorphicAt

/-- If a function is meromorphic in normal form on `U`, then its divisor is
non-negative iff it is analytic. -/
theorem MeromorphicNFOn.nonneg_divisor_iff_analyticOnNhd [CompleteSpace E]
    (h₁f : MeromorphicNFOn f U) :
    0 ≤ MeromorphicOn.divisor f U ↔ AnalyticOnNhd 𝕜 f U := by
  constructor <;> intro h
  · intro x hx
    rw [← (h₁f x hx).order_nonneg_iff_analyticAt]
    have := h x
    simp only [DivisorOn.coe_zero, Pi.zero_apply, h₁f.meromorphicOn, hx,
      MeromorphicOn.divisor_apply, le_refl, implies_true, WithTop.le_untopD_iff,
      WithTop.coe_zero] at this
    assumption
  · intro x
    by_cases hx : x ∈ U
    · simp only [DivisorOn.coe_zero, Pi.zero_apply, h₁f.meromorphicOn, hx,
        MeromorphicOn.divisor_apply, le_refl, implies_true, WithTop.le_untopD_iff,
        WithTop.coe_zero]
      exact (h₁f x hx).order_nonneg_iff_analyticAt.2 (h x hx)
    · simp [h₁f.meromorphicOn, hx]

/- Analytic functions are meromorphic in normal form. -/
theorem AnalyticOnNhd.meromorphicNFOn (h₁f : AnalyticOnNhd 𝕜 f U) :
    MeromorphicNFOn f U := fun z hz ↦ (h₁f z hz).meromorphicNFAt

/-!
## Level sets of the order function
-/

/-- Criterion to ensure that the order of a meromorphic function in normal form
is not infinity. See `MeromorphicOn.exists_order_ne_top_iff_forall` for a related
criterion for arbitrarymeromorphic functions. -/
theorem MeromorphicNFOn.order_ne_top_if_exists_value_ne_zero (h₁f : MeromorphicNFOn f U)
    (h₂f : ∃ u : U, f u ≠ 0) (hU : IsConnected U) :
    ∀ u : U, (h₁f u u.2).meromorphicAt.order ≠ ⊤ := by
  rw [← h₁f.meromorphicOn.exists_order_ne_top_iff_forall hU]
  obtain ⟨u, hu⟩ := h₂f
  use u
  rw [← (h₁f u u.2).order_eq_zero_iff] at hu
  simp [hu]

/-!
## Divisors of meromorphic functions in normal form.
-/

theorem MeromorphicNFOn.zero_set_eq_divisor_support [CompleteSpace E] (h₁f : MeromorphicNFOn f U)
    (h₂f : ∃ u : U, f u ≠ 0) (hU : IsConnected U) :
    U ∩ f⁻¹' {0} = (Function.support (MeromorphicOn.divisor f U)) := by
  ext u
  constructor <;> intro hu
  · simp_all only [ne_eq, Subtype.exists, exists_prop, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Function.mem_support, h₁f.meromorphicOn, MeromorphicOn.divisor_apply,
      WithTop.untopD_eq_self_iff, WithTop.coe_zero, (h₁f u hu.1).order_eq_zero_iff,
      not_true_eq_false, false_or]
    apply h₁f.order_ne_top_if_exists_value_ne_zero _ hU ⟨u, hu.1⟩
    obtain ⟨a, ha⟩ := h₂f
    use ⟨a, ha.1⟩, ha.2
  · simp only [Function.mem_support, ne_eq] at hu
    constructor
    · exact (MeromorphicOn.divisor f U).supportWithinDomain hu
    · rw [Set.mem_preimage, Set.mem_singleton_iff]
      have := (h₁f u ((MeromorphicOn.divisor f U).supportWithinDomain hu)).order_eq_zero_iff.not
      simp only [h₁f.meromorphicOn, (MeromorphicOn.divisor f U).supportWithinDomain hu,
        MeromorphicOn.divisor_apply, WithTop.untopD_eq_self_iff, WithTop.coe_zero, not_or] at hu
      simp_all [this, hu.1]

theorem MeromorphicNFOn_of_mul_analytic'
  {f : 𝕜 → E}
  {g : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁g : AnalyticOnNhd 𝕜 g U)
  (h₂g : ∀ u : U, g u ≠ 0)
  (h₁f : MeromorphicNFOn f U) :
  MeromorphicNFOn (g • f) U := by
  intro z hz
  apply MeromorphicNFAt.meromorphicNFAt_of_smul_analytic (h₁f z hz) (h₁g z hz)
  exact h₂g ⟨z, hz⟩

/- Make strongly MeromorphicOn -/
noncomputable def makeMeromorphicNFOn
  (f : 𝕜 → 𝕜) (U : Set 𝕜) :
  𝕜 → 𝕜 := by
  intro z
  by_cases hz : z ∈ U
  · exact toMeromorphicNFAt f z z
  · exact f z

theorem makeMeromorphicNFOn_changeDiscrete [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z₀ : 𝕜}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  makeMeromorphicNFOn f U =ᶠ[𝓝[≠] z₀] f := by
  apply Filter.eventually_iff_exists_mem.2
  let A := (hf z₀ hz₀).eventually_analyticAt
  obtain ⟨V, h₁V, h₂V⟩  := Filter.eventually_iff_exists_mem.1 A
  use V
  constructor
  · assumption
  · intro v hv
    unfold makeMeromorphicNFOn
    by_cases h₂v : v ∈ U
    · simp [h₂v]
      let B := (h₂V v hv).meromorphicNFAt
      let Z := toMeromorphicNFAt_eq_self.1 B
      rw [eq_comm]
      rw [← Z]
    · simp [h₂v]

theorem makeMeromorphicNFOn_changeDiscrete' [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z₀ : 𝕜}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  makeMeromorphicNFOn f U =ᶠ[𝓝 z₀] toMeromorphicNFAt f z₀ := by
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  · apply Filter.EventuallyEq.trans (makeMeromorphicNFOn_changeDiscrete hf hz₀)
    exact MeromorphicAt.eq_nhdNE_toMeromorphicNFAt (hf z₀ hz₀)
  · rw [makeMeromorphicNFOn]
    simp [hz₀]

theorem makeMeromorphicNFOn_changeDiscrete'' [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  f =ᶠ[Filter.codiscreteWithin U] makeMeromorphicNFOn f U := by

  rw [Filter.eventuallyEq_iff_exists_mem]
  use { x | AnalyticAt 𝕜 f x }, hf.analyticAt_codiscreteWithin
  intro x hx
  simp at hx
  rw [makeMeromorphicNFOn]
  by_cases h₁x : x ∈ U
  · simp [h₁x]
    rw [← toMeromorphicNFAt_eq_self.1 hx.meromorphicNFAt]
  · simp [h₁x]

theorem MeromorphicNFOn_of_makeMeromorphicNFOn [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  MeromorphicNFOn (makeMeromorphicNFOn f U) U := by
  intro z hz
  let A := makeMeromorphicNFOn_changeDiscrete' hf hz
  rw [meromorphicNFAt_congr A]
  exact meromorphicNFAt_toMeromorphicNFAt

theorem makeMeromorphicNFOn_changeOrder [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z₀ : 𝕜}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  (MeromorphicNFOn_of_makeMeromorphicNFOn hf z₀ hz₀).meromorphicAt.order = (hf z₀ hz₀).order := by
  apply MeromorphicAt.order_congr
  exact makeMeromorphicNFOn_changeDiscrete hf hz₀

theorem MeromorphicOn.divisor_of_makeMeromorphicNFOn [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  divisor f U = divisor (makeMeromorphicNFOn f U) U := by
  ext z
  by_cases hz : z ∈ U
  · simp [hf, (MeromorphicNFOn_of_makeMeromorphicNFOn hf).meromorphicOn, hz]
    congr 1
    apply MeromorphicAt.order_congr
    exact Filter.EventuallyEq.symm (makeMeromorphicNFOn_changeDiscrete hf hz)
  · simp [hz]
