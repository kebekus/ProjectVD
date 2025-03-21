import Mathlib.Analysis.Meromorphic.Divisor.MeromorphicFunction
import VD.ToMathlib.MeromorphicNFAt
import VD.Divisor_MeromorphicOn

open Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E}
  {x : 𝕜}
  {U : Set 𝕜}


/-- If `f` is meromorphic in normal form, then so is its inverse. -/
theorem MeromorphicNFAt.inv {f : 𝕜 → 𝕜} (hf : MeromorphicNFAt f x) :
    MeromorphicNFAt f⁻¹ x := by
  rcases hf with h | ⟨n, g, h₁, h₂, h₃⟩
  · left
    filter_upwards [h] with x hx
    simp [hx]
  · right
    use -n, g⁻¹, h₁.inv h₂, (by simp_all)
    filter_upwards [h₃] with y hy
    simp only [Pi.inv_apply, hy, Pi.smul_apply', Pi.pow_apply, smul_eq_mul, mul_inv_rev, zpow_neg]
    ring_nf

/-- A function to 𝕜 is meromorphic in normal form at a point iff its inverse is. -/
theorem meromorphicNFAt_iff_meromorphicNFAt_inv {f : 𝕜 → 𝕜} :
    MeromorphicNFAt f x ↔ MeromorphicNFAt f⁻¹ x := by
  constructor
  · exact MeromorphicNFAt.inv
  · nth_rw 2 [← inv_inv f]
    exact MeromorphicNFAt.inv

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

/-- A function to 𝕜 is meromorphic in normal form on `U` iff its inverse is. -/
theorem meromorphicNFOn_iff_meromorphicNFOn_inv {f : 𝕜 → 𝕜} :
    MeromorphicNFOn f U ↔ MeromorphicNFOn f⁻¹ U := by
  constructor
  · exact fun h x hx ↦ meromorphicNFAt_iff_meromorphicNFAt_inv.1 (h x hx)
  · exact fun h x hx ↦ meromorphicNFAt_iff_meromorphicNFAt_inv.2 (h x hx)

/-!
## Continuous extension and conversion to normal form
-/

variable (f U) in
/-- If `f` is meromorphic on `U`, convert `f` to normal form on `U` by changing its values along
a discrete subset within `U`. Otherwise, returns the 0 function. -/
noncomputable def toMeromorphicNFOn :
    𝕜 → E := by
  by_cases h₁f : MeromorphicOn f U
  · intro z
    by_cases hz : z ∈ U
    · exact toMeromorphicNFAt f z z
    · exact f z
  · exact 0

/-- If `f` is not meromorphic on `U`, conversion to normal form  maps the function to `0`. -/
@[simp] lemma toMeromorphicNFOn_of_not_meromorphicOn (hf : ¬MeromorphicOn f U) :
    toMeromorphicNFOn f U = 0 := by
  simp [toMeromorphicNFOn, hf]

/-- Conversion to normal form on `U` does not change values outside of `U`. -/
@[simp] lemma toMeromorphicNFOn_eq_self_on_compl (hf : MeromorphicOn f U) :
    Set.EqOn f (toMeromorphicNFOn f U) Uᶜ := by
  intro x hx
  simp_all [toMeromorphicNFOn]

/-- Conversion to normal form on `U` changes the value only along a discrete subset of `U`. -/
theorem toMeromorphicNFOn_eqOn_codiscrete [CompleteSpace E] (hf : MeromorphicOn f U) :
    f =ᶠ[Filter.codiscreteWithin U] toMeromorphicNFOn f U := by
  have : U ∈ Filter.codiscreteWithin U := by
    simp [mem_codiscreteWithin.2]
  filter_upwards [hf.analyticAt_codiscreteWithin, this] with a h₁a h₂a
  simp [toMeromorphicNFOn, hf, ← toMeromorphicNFAt_eq_self.1 h₁a.meromorphicNFAt]

/-- Conversion to normal form on `U` does not affect the divisor. -/
theorem divisor_toMeromorphicNFOn [CompleteSpace E] (hf : MeromorphicOn f U) :
    MeromorphicOn.divisor f U = MeromorphicOn.divisor (toMeromorphicNFOn f U) U := by
  rw [← hf.divisor_congr_codiscreteWithin (toMeromorphicNFOn_eqOn_codiscrete hf)]
  exact toMeromorphicNFOn_eq_self_on_compl hf

/-- If `f` is meromorphic on `U` and `x ∈ U`, then `f` and its conversion to
normal form on `U` agree in a punctured neighborhood of `x`. -/
theorem MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdNE [CompleteSpace E]
    (hf : MeromorphicOn f U) (hx : x ∈ U) :
    f =ᶠ[𝓝[≠] x] toMeromorphicNFOn f U := by
  filter_upwards [(hf x hx).eventually_analyticAt] with a ha
  simp [toMeromorphicNFOn, hf, ← toMeromorphicNFAt_eq_self.1 ha.meromorphicNFAt]

/-- If `f` is meromorphic on `U` and `x ∈ U`, then conversion to normal form at
`x` and conversion to normal form on `U` agree in a neighborhood of `x`. -/
theorem toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhdNE [CompleteSpace E] (hf : MeromorphicOn f U)
    (hx : x ∈ U) :
    toMeromorphicNFOn f U =ᶠ[𝓝 x] toMeromorphicNFAt f x := by
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  exact (hf.toMeromorphicNFOn_eq_self_on_nhdNE hx).symm.trans (hf x hx).eq_nhdNE_toMeromorphicNFAt
  simp [toMeromorphicNFOn, hf, hx]

variable (f U) in
/-- After conversion to normal form at `x`, the function has normal form. -/
theorem meromorphicNFOn_toMeromorphicNFOn [CompleteSpace E] :
    MeromorphicNFOn (toMeromorphicNFOn f U) U := by
  by_cases hf : MeromorphicOn f U
  · intro z hz
    rw [meromorphicNFAt_congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhdNE hf hz)]
    exact meromorphicNFAt_toMeromorphicNFAt
  · simp [hf]
    apply AnalyticOnNhd.meromorphicNFOn
    exact analyticOnNhd_const

/-- If `f` has normal form on `U`, then `f` equals `toMeromorphicNFOn f U`. -/
@[simp] theorem toMeromorphicNFOn_eq_self [CompleteSpace E] :
    MeromorphicNFOn f U ↔ f = toMeromorphicNFOn f U := by
  constructor <;> intro h
  · ext x
    by_cases hx : x ∈ U
    · simp only [toMeromorphicNFOn, h.meromorphicOn, ↓reduceDIte, hx]
      rw [← toMeromorphicNFAt_eq_self.1 (h x hx)]
    · simp [toMeromorphicNFOn, h.meromorphicOn, hx]
  · rw [h]
    apply meromorphicNFOn_toMeromorphicNFOn


/- ######################################################## -/

theorem toMeromorphicNFOn_changeOrder [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z₀ : 𝕜}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  ((meromorphicNFOn_toMeromorphicNFOn f U) z₀ hz₀).meromorphicAt.order = (hf z₀ hz₀).order := by
  apply MeromorphicAt.order_congr
  exact (hf.toMeromorphicNFOn_eq_self_on_nhdNE hz₀).symm


theorem MeromorphicOn.divisor_of_toMeromorphicNFOn [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  divisor f U = divisor (toMeromorphicNFOn f U) U := by
  ext z
  by_cases hz : z ∈ U
  · simp [hf, (meromorphicNFOn_toMeromorphicNFOn f U).meromorphicOn, hz]
    congr 1
    apply MeromorphicAt.order_congr
    exact toMeromorphicNFOn_eq_self_on_nhdNE hf hz
  · simp [hz]
