import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Meromorphic.Divisor.Basic
import VD.mathlibAddOn
import VD.meromorphicOn
import VD.stronglyMeromorphicOn

open scoped Interval Topology
open Classical
open Real Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- TODO: Remove the assumption CompleteSpace E.

noncomputable def MeromorphicOn.divisor [CompleteSpace E] {f : 𝕜 → E} {U : Set 𝕜} (hf : MeromorphicOn f U) :
  DivisorOn U where

  toFun := fun z ↦ if hz : z ∈ U then ((hf z hz).order.untopD 0 : ℤ) else 0

  supportWithinDomain' := by
    intro z hz
    simp at hz
    by_contra h₂z
    simp [h₂z] at hz

  supportDiscreteWithinDomain' := by
    filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
      hf.codiscrete_setOf_order_eq_zero_or_top]
    intro _ _
    simp_all only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_right,
      exists_eq_right, Pi.zero_apply, dite_eq_right_iff, WithTop.untopD_eq_self_iff,
      WithTop.coe_zero]
    tauto

theorem MeromorphicOn.divisor_def [CompleteSpace E]
  {f : 𝕜 → E}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U) :
  hf.divisor z = if hz : z ∈ U then ((hf z hz).order.untopD 0 : ℤ) else 0 := by
  rfl

theorem MeromorphicOn.divisor_def₁ [CompleteSpace E]
  {f : 𝕜 → E}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (hz : z ∈ U) :
  hf.divisor z = ((hf z hz).order.untopD 0 : ℤ) := by
  simp_all [hf.divisor_def]

theorem MeromorphicOn.divisor_def₂ [CompleteSpace E]
  {f : 𝕜 → E}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (hz : z ∈ U)
  (h₂f : (hf z hz).order ≠ ⊤) :
  hf.divisor z = (hf z hz).order.untop h₂f := by
  simp_all [hf.divisor_def]
  refine (WithTop.eq_untop_iff h₂f).mpr ?_
  exact untop'_of_ne_top h₂f

-- Divisor depends on codiscrete

theorem MeromorphicOn.divisor_mul₀  [CompleteSpace 𝕜]
  {f₁ f₂ : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z : 𝕜}
  (hz : z ∈ U)
  (h₁f₁ : MeromorphicOn f₁ U)
  (h₂f₁ : (h₁f₁ z hz).order ≠ ⊤)
  (h₁f₂ : MeromorphicOn f₂ U)
  (h₂f₂ : (h₁f₂ z hz).order ≠ ⊤) :
  (h₁f₁.mul h₁f₂).divisor z = h₁f₁.divisor z + h₁f₂.divisor z := by
  rw [MeromorphicOn.divisor_def₂ h₁f₁ hz h₂f₁]
  rw [MeromorphicOn.divisor_def₂ h₁f₂ hz h₂f₂]
  have B : ((h₁f₁.mul h₁f₂) z hz).order ≠ ⊤ := by
    rw [MeromorphicAt.order_mul (h₁f₁ z hz) (h₁f₂ z hz)]
    simp only [ne_eq, LinearOrderedAddCommGroupWithTop.add_eq_top, not_or]
    tauto
  rw [MeromorphicOn.divisor_def₂ (h₁f₁.mul h₁f₂) hz B]
  simp_rw [MeromorphicAt.order_mul (h₁f₁ z hz) (h₁f₂ z hz)]
  rw [untop_add]

theorem MeromorphicOn.divisor_mul [CompleteSpace 𝕜]
  {f₁ f₂ : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁f₁ : MeromorphicOn f₁ U)
  (h₂f₁ : ∀ z, (hz : z ∈ U) → (h₁f₁ z hz).order ≠ ⊤)
  (h₁f₂ : MeromorphicOn f₂ U)
  (h₂f₂ : ∀ z, (hz : z ∈ U) → (h₁f₂ z hz).order ≠ ⊤) :
  (h₁f₁.mul h₁f₂).divisor = h₁f₁.divisor + h₁f₂.divisor := by
  ext z
  by_cases hz : z ∈ U
  · simp only [DivisorOn.coe_add, Pi.add_apply]
    rw [MeromorphicOn.divisor_mul₀ hz h₁f₁ (h₂f₁ z hz) h₁f₂ (h₂f₂ z hz)]
  · simp only [DivisorOn.coe_add, Pi.add_apply]
    rw [Function.nmem_support.mp (fun a => hz (h₁f₁.divisor.supportWithinDomain a))]
    rw [Function.nmem_support.mp (fun a => hz (h₁f₂.divisor.supportWithinDomain a))]
    rw [Function.nmem_support.mp (fun a => hz ((h₁f₁.mul h₁f₂).divisor.supportWithinDomain a))]
    simp

theorem MeromorphicOn.divisor_inv [CompleteSpace 𝕜]
  {f: 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁f : MeromorphicOn f U) :
  h₁f.inv.divisor = -h₁f.divisor := by
  ext z
  by_cases hz : z ∈ U
  · simp
    rw [MeromorphicOn.divisor_def₁ h₁f hz]
    rw [MeromorphicOn.divisor_def₁ h₁f.inv hz]
    rw [MeromorphicAt.order_inv]
    simp
    by_cases h₂f : (h₁f z hz).order = ⊤
    · simp [h₂f]
    · let A := untop'_of_ne_top (d := 0) h₂f
      rw [← A]
      exact rfl
  · simp
    rw [MeromorphicOn.divisor_def]
    rw [MeromorphicOn.divisor_def]
    simp [hz]

theorem MeromorphicOn.divisor_add_const₁  [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (a : 𝕜) :
  0 ≤ hf.divisor z → 0 ≤ (hf.add (MeromorphicOn.const a)).divisor z := by
  intro h

  -- Trivial case: z ∉ U
  by_cases hz : z ∉ U
  · rw [MeromorphicOn.divisor_def]
    simp [hz]

  -- Non-trivial case: z ∈ U
  rw [MeromorphicOn.divisor_def]
  simp at hz
  simp [hz]

  by_cases h₁f : (hf z hz).order = ⊤
  · have : f + (fun z ↦ a) =ᶠ[𝓝[≠] z] (fun z ↦ a) := by
      rw [MeromorphicAt.order_eq_top_iff] at h₁f
      rw [eventually_nhdsWithin_iff] at h₁f
      rw [eventually_nhds_iff] at h₁f
      obtain ⟨t, ht⟩ := h₁f
      rw [eventuallyEq_nhdsWithin_iff]
      rw [eventually_nhds_iff]
      use t
      simp [ht]
      tauto
    rw [((hf z hz).add (MeromorphicAt.const a z)).order_congr this]

    by_cases ha: (MeromorphicAt.const a z).order = ⊤
    · simp [ha]
    · rw [WithTop.le_untopD_iff]
      apply AnalyticAt.meromorphicAt_order_nonneg
      exact analyticAt_const
      tauto

  · rw [WithTop.le_untopD_iff]
    let A := (hf z hz).order_add (MeromorphicAt.const a z)
    have : 0 ≤ min (hf z hz).order (MeromorphicAt.const a z).order := by
      apply le_min
      --
      rw [MeromorphicOn.divisor_def] at h
      simp [hz] at h
      let V := untop'_of_ne_top (d := 0) h₁f
      rw [← V]
      simp [h]
      --
      apply AnalyticAt.meromorphicAt_order_nonneg
      exact analyticAt_const
    exact le_trans this A
    tauto

theorem MeromorphicOn.divisor_add_const₂ [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (a : 𝕜) :
  hf.divisor z < 0 → (hf.add (MeromorphicOn.const a)).divisor z < 0 := by
  intro h

  by_cases hz : z ∉ U
  · have : hf.divisor z = 0 := by
      rw [MeromorphicOn.divisor_def]
      simp_all
    rw [this] at h
    tauto

  simp at hz
  rw [MeromorphicOn.divisor_def] at *
  simp [hz]
  simp [hz] at h

  have : (hf z hz).order = (((hf.add (MeromorphicOn.const a))) z hz).order := by
    have t₀ : (hf z hz).order < (0 : ℤ) := by
        by_contra hCon
        simp only [not_lt] at hCon
        rw [←WithTop.le_untopD_iff (b := 0)] at hCon
        exact Lean.Omega.Int.le_lt_asymm hCon h
        tauto
    rw [← MeromorphicAt.order_add_of_ne_orders (hf z hz) (MeromorphicAt.const a z)]
    simp

    by_cases ha: (MeromorphicAt.const a z).order = ⊤
    · simp [ha]
    · calc (hf z hz).order
      _ ≤ 0 := t₀.le
      _ ≤ (MeromorphicAt.const a z).order := by
        apply AnalyticAt.meromorphicAt_order_nonneg
        exact analyticAt_const

    apply ne_of_lt
    calc (hf z hz).order
      _ < 0 := by exact t₀
      _ ≤ (MeromorphicAt.const a z).order := by
        apply AnalyticAt.meromorphicAt_order_nonneg
        exact analyticAt_const
  rwa [this] at h

theorem MeromorphicOn.divisor_add_const₃ [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (a : 𝕜) :
  hf.divisor z < 0 → (hf.add (MeromorphicOn.const a)).divisor z = hf.divisor z := by
  intro h

  by_cases hz : z ∉ U
  · have : hf.divisor z = 0 := by
      rw [MeromorphicOn.divisor_def]
      simp_all
    rw [this] at h
    tauto

  rw [MeromorphicOn.divisor_def]
  simp at hz
  simp [hz]

  have : (hf z hz).order = (((hf.add (MeromorphicOn.const a))) z hz).order := by
    have t₀ : (hf z hz).order < (0 : ℤ) := by
        by_contra hCon
        simp only [not_lt] at hCon
        rw [←WithTop.le_untopD_iff (b := 0)] at hCon
        rw [MeromorphicOn.divisor_def] at h
        simp [hz] at h
        exact Lean.Omega.Int.le_lt_asymm hCon h
        tauto
    rw [← MeromorphicAt.order_add_of_ne_orders (hf z hz) (MeromorphicAt.const a z)]
    simp

    by_cases ha: (MeromorphicAt.const a z).order = ⊤
    · simp [ha]
    · calc (hf z hz).order
      _ ≤ 0 := t₀.le
      _ ≤ (MeromorphicAt.const a z).order := by
        apply AnalyticAt.meromorphicAt_order_nonneg
        exact analyticAt_const

    apply ne_of_lt
    calc (hf z hz).order
      _ < 0 := by exact t₀
      _ ≤ (MeromorphicAt.const a z).order := by
        apply AnalyticAt.meromorphicAt_order_nonneg
        exact analyticAt_const
  rw [← this]
  exact Eq.symm (divisor_def₁ hf hz)

theorem MeromorphicOn.divisor_of_makeStronglyMeromorphicOn [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  hf.divisor = (stronglyMeromorphicOn_of_makeStronglyMeromorphicOn hf).meromorphicOn.divisor := by
  unfold MeromorphicOn.divisor
  simp
  funext z
  by_cases hz : z ∈ U
  · simp [hz]
    congr 1
    apply MeromorphicAt.order_congr
    exact EventuallyEq.symm (makeStronglyMeromorphicOn_changeDiscrete hf hz)
  · simp [hz]



-- STRONGLY MEROMORPHIC THINGS

/- Strongly MeromorphicOn of non-negative order is analytic -/
theorem StronglyMeromorphicOn.analyticOnNhd [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁f : StronglyMeromorphicOn f U)
  (h₂f : ∀ x, (hx : x ∈ U) → 0 ≤ h₁f.meromorphicOn.divisor x) :
  AnalyticOnNhd 𝕜 f U := by

  apply StronglyMeromorphicOn.analytic
  intro z hz
  let A := h₂f z hz
  rw [MeromorphicOn.divisor_def] at A
  simp [hz] at A

  by_cases h : (h₁f z hz).meromorphicAt.order = ⊤
  · rw [h]
    simp
  · rw [WithTop.le_untopD_iff] at A
    tauto
    tauto
  assumption


theorem StronglyMeromorphicOn.support_divisor [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁f : StronglyMeromorphicOn f U)
  (h₂f : ∃ u : U, f u ≠ 0)
  (hU : IsConnected U) :
  U ∩ f⁻¹' {0} = (Function.support h₁f.meromorphicOn.divisor) := by

  ext u
  constructor
  · intro hu
    simp_all
    rw [MeromorphicOn.divisor_def]
    simp [hu.1]
    constructor
    · rw [(h₁f u hu.1).order_eq_zero_iff]
      tauto
    · have : ∃ u : U, f u ≠ 0 := by
        obtain ⟨a, ha⟩ := h₂f
        use ⟨a, ha.1⟩
        exact ha.2
      exact h₁f.order_ne_top hU this ⟨u, hu.1⟩
  · intro hu
    simp at hu
    let A := h₁f.meromorphicOn.divisor.supportWithinDomain hu
    constructor
    · exact h₁f.meromorphicOn.divisor.supportWithinDomain hu
    · simp
      let B := (h₁f u A).order_eq_zero_iff.not
      simp at B
      rw [← B]
      rw [MeromorphicOn.divisor_def] at hu
      simp [A] at hu
      exact hu.1
