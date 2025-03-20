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

/-- Analytic functions are meromorphic in normal form. -/
theorem AnalyticOnNhd.meromorphicNFOn (h₁f : AnalyticOnNhd 𝕜 f U) :
    MeromorphicNFOn f U := fun z hz ↦ (h₁f z hz).meromorphicNFAt

/-!
## Divisors and zeros of meromorphic functions in normal form.
-/

/-- If `f` is meromorphic in normal form on `U` and nowhere locally constant zero, then its
zero set equals the support of the associated divisor. -/
theorem MeromorphicNFOn.zero_set_eq_divisor_support [CompleteSpace E] (h₁f : MeromorphicNFOn f U)
    (h₂f : ∀ u : U, (h₁f u u.2).meromorphicAt.order ≠ ⊤) :
    U ∩ f⁻¹' {0} = (Function.support (MeromorphicOn.divisor f U)) := by
  ext u
  constructor <;> intro hu
  · simp_all only [ne_eq, Subtype.exists, exists_prop, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Function.mem_support, h₁f.meromorphicOn, MeromorphicOn.divisor_apply,
      WithTop.untopD_eq_self_iff, WithTop.coe_zero, (h₁f u hu.1).order_eq_zero_iff,
      not_true_eq_false, false_or]
    exact h₂f ⟨u, hu.1⟩
  · simp only [Function.mem_support, ne_eq] at hu
    constructor
    · exact (MeromorphicOn.divisor f U).supportWithinDomain hu
    · rw [Set.mem_preimage, Set.mem_singleton_iff]
      have := (h₁f u ((MeromorphicOn.divisor f U).supportWithinDomain hu)).order_eq_zero_iff.not
      simp only [h₁f.meromorphicOn, (MeromorphicOn.divisor f U).supportWithinDomain hu,
        MeromorphicOn.divisor_apply, WithTop.untopD_eq_self_iff, WithTop.coe_zero, not_or] at hu
      simp_all [this, hu.1]

/-!
## Criteria to guarantee normal form
-/

/-- If `f` is any function and `g` is analytic without zero on `U`, then `f` is meromorphic in
normal form on `U` iff `g • f` is meromorphic in normal form on `U`. -/
theorem meromorphicNFOn_smul_iff_right_of_analyticAt {g : 𝕜 → 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : ∀ u : U, g u ≠ 0) :
    MeromorphicNFOn (g • f) U ↔ MeromorphicNFOn f U := by
  constructor <;> intro h z hz
  · rw [meromorphicNFAt_iff_meromorphicNFAt_of_smul_analytic (h₁g z hz) (h₂g ⟨z, hz⟩)]
    exact h z hz
  · apply MeromorphicNFAt.meromorphicNFAt_of_smul_analytic (h z hz) (h₁g z hz)
    exact h₂g ⟨z, hz⟩

/-- If `f` is any function and `g` is analytic without zero in `U`, then `f` is meromorphic in
normal form on `U` iff `g * f` is meromorphic in normal form on `U`. -/
theorem meromorphicNFOn_mul_iff_right {f g : 𝕜 → 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : ∀ u : U, g u ≠ 0) :
    MeromorphicNFOn (g * f) U ↔ MeromorphicNFOn f U := by
  rw [← smul_eq_mul]
  exact meromorphicNFOn_smul_iff_right_of_analyticAt h₁g h₂g

/-- If `f` is any function and `g` is analytic without zero in `U`, then `f` is meromorphic in
normal form on `U` iff `f * g` is meromorphic in normal form on `U`. -/
theorem meromorphicNFAt_mul_iff_left {f g : 𝕜 → 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : ∀ u : U, g u ≠ 0) :
    MeromorphicNFOn (f * g) U ↔ MeromorphicNFOn f U := by
  rw [mul_comm, ← smul_eq_mul]
  exact meromorphicNFOn_smul_iff_right_of_analyticAt h₁g h₂g

/-!
## Continuous extension and conversion to normal form
-/

variable (f U) in
/-- If `f` is meromorphic on `U`, convert `f` to normal form on `U` by changing its values along
a discrete subset within `U`. Otherwise, returns the 0 function. -/
noncomputable def toMeromorphicNFOn :
    𝕜 → E := by
  by_cases hf : MeromorphicOn f U
  · exact fun z ↦ toMeromorphicNFAt f z z
  · exact 0

/- ######################################################## -/

theorem toMeromorphicNFOn_changeDiscrete [CompleteSpace E] (hf : MeromorphicOn f U) (hx : x ∈ U) :
    toMeromorphicNFOn f U =ᶠ[𝓝[≠] x] f := by
  filter_upwards [(hf x hx).eventually_analyticAt] with a ha
  simp [toMeromorphicNFOn, hf, ← toMeromorphicNFAt_eq_self.1 ha.meromorphicNFAt]

theorem toMeromorphicNFOn_changeDiscrete' [CompleteSpace E] (hf : MeromorphicOn f U)
    (hx : x ∈ U) :
    toMeromorphicNFOn f U =ᶠ[𝓝 x] toMeromorphicNFAt f x := by
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE ((toMeromorphicNFOn_changeDiscrete hf hx).trans
    (hf x hx).eq_nhdNE_toMeromorphicNFAt)
  simp [toMeromorphicNFOn, hf]

theorem toMeromorphicNFOn_changeDiscrete'' [CompleteSpace E] (hf : MeromorphicOn f U) :
    f =ᶠ[Filter.codiscreteWithin U] toMeromorphicNFOn f U := by
  have : U ∈ Filter.codiscreteWithin U := by
    simp [mem_codiscreteWithin.2]
  filter_upwards [hf.analyticAt_codiscreteWithin, this] with a h₁a h₂a
  simp [toMeromorphicNFOn, hf, ← toMeromorphicNFAt_eq_self.1 h₁a.meromorphicNFAt]

theorem MeromorphicNFOn_of_toMeromorphicNFOn [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  MeromorphicNFOn (toMeromorphicNFOn f U) U := by
  intro z hz

  rw [meromorphicNFAt_congr (toMeromorphicNFOn_changeDiscrete' hf hz)]
  exact meromorphicNFAt_toMeromorphicNFAt

theorem toMeromorphicNFOn_changeOrder [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z₀ : 𝕜}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  (MeromorphicNFOn_of_toMeromorphicNFOn hf z₀ hz₀).meromorphicAt.order = (hf z₀ hz₀).order := by
  apply MeromorphicAt.order_congr
  exact toMeromorphicNFOn_changeDiscrete hf hz₀

theorem MeromorphicOn.divisor_of_toMeromorphicNFOn [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  divisor f U = divisor (toMeromorphicNFOn f U) U := by
  ext z
  by_cases hz : z ∈ U
  · simp [hf, (MeromorphicNFOn_of_toMeromorphicNFOn hf).meromorphicOn, hz]
    congr 1
    apply MeromorphicAt.order_congr
    exact Filter.EventuallyEq.symm (toMeromorphicNFOn_changeDiscrete hf hz)
  · simp [hz]
