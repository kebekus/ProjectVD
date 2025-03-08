import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.DiscreteSubset
import VD.divisor
import VD.mathlibAddOn
import VD.meromorphicOn
import VD.stronglyMeromorphicOn
import VD.ToMathlib.meromorphicOn_levelSetOfOrder

open scoped Interval Topology
open Real Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- TODO: Remove the assumption CompleteSpace E.

/-
lemma ContinuousAt.x {f g : 𝕜 → E} {z₀ : 𝕜} (hf : ContinuousAt f z₀) (hg : ContinuousAt f z₀)
    (hfg : f =ᶠ[𝓝[≠] z₀] g) :
    f z₀ = g z₀ := by
  by_contra h
  sorry


theorem ContinuousAt.y {f g : 𝕜 → E} {z₀ : 𝕜} (hf : ContinuousAt f z₀) (hg : ContinuousAt f z₀) :
    f =ᶠ[𝓝[≠] z₀] g ↔ f =ᶠ[𝓝 z₀] g := by
  constructor
  · intro h
    apply eventuallyEq_nhdsWithin_of_eventuallyEq_nhds h
    sorry
  · intro h
    apply eventuallyEq_nhdsWithin_iff.mpr
    filter_upwards [h]
    tauto

theorem MeromorphicAt.order_eq_zero_iff {f : 𝕜 → E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    hf.order = 0 ↔ (∃ g, (ContinuousAt g z₀) ∧ (g z₀ ≠ 0) ∧ f =ᶠ[𝓝[≠] z₀] g ) := by
  constructor
  · intro h₂f
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (hf.order_eq_int_iff 0).1 h₂f
    use g, h₁g.continuousAt, h₂g
    simp only [zpow_zero, one_smul] at h₃g
    exact h₃g
  · intro h₂f
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₂f
    apply (hf.order_eq_int_iff 0).2
    by_cases h₁ : hf.order = ⊤
    · rw [hf.order_eq_top_iff] at h₁
      have : ∀ᶠ (z : 𝕜) in 𝓝[≠] z₀, g z = 0 := by
        filter_upwards [h₁, h₃g]
        intro a h₁a h₂a
        rw [← h₂a, h₁a]
      have : g z₀ = 0 := by

        sorry
      tauto
    sorry

theorem MeromorphicAt.order_eq_zero_iff {f : 𝕜 → E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    hf.order ≥ 0 ↔ (∃ g, (ContinuousAt g z₀) ∧ f =ᶠ[𝓝[≠] z₀] g ) := by
  constructor
  · intro h₂f
    let n := hf.order
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (hf.order_eq_int_iff n).1 h₂f
    use g, h₁g.continuousAt, h₂g
    simp only [zpow_zero, one_smul] at h₃g
    exact h₃g
  · intro h₂f
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₂f
    apply (hf.order_eq_int_iff 0).2
    by_cases h₁ : hf.order = ⊤
    · rw [hf.order_eq_top_iff] at h₁
      have : ∀ᶠ (z : 𝕜) in 𝓝[≠] z₀, g z = 0 := by
        filter_upwards [h₁, h₃g]
        intro a h₁a h₂a
        rw [← h₂a, h₁a]
      have : g z₀ = 0 := by

        sorry
      tauto
    sorry
-/


noncomputable def MeromorphicOn.divisor [CompleteSpace E] {f : 𝕜 → E} {U : Set 𝕜} (hf : MeromorphicOn f U) :
  Divisor U where

  toFun := by
    intro z
    if hz : z ∈ U then
      exact ((hf z hz).order.untopD 0 : ℤ)
    else
      exact 0

  supportWithinDomain := by
    intro z hz
    simp at hz
    by_contra h₂z
    simp [h₂z] at hz

  supportDiscreteWithinDomain := by
    filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
      hf.codiscrete_setOf_order_eq_zero_or_top]
    intro _ _
    simp_all only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_right,
      exists_eq_right, Pi.zero_apply, dite_eq_right_iff, WithTop.untopD_eq_self_iff,
      WithTop.coe_zero]
    tauto

theorem MeromorphicOn.divisor_def₁ [CompleteSpace E]
  {f : 𝕜 → E}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (hz : z ∈ U) :
  hf.divisor z = ((hf z hz).order.untopD 0 : ℤ) := by
  unfold MeromorphicOn.divisor
  simp [hz]


theorem MeromorphicOn.divisor_def₂ [CompleteSpace E]
  {f : 𝕜 → E}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (hz : z ∈ U)
  (h₂f : (hf z hz).order ≠ ⊤) :
  hf.divisor z = (hf z hz).order.untop h₂f := by
  unfold MeromorphicOn.divisor
  simp [hz]
  rw [WithTop.untopD_eq_iff]
  left
  exact Eq.symm (WithTop.coe_untop (hf z hz).order h₂f)


theorem MeromorphicOn.divisor_mul₀  [CompleteSpace 𝕜]
  {f₁ f₂ : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z : 𝕜}
  (hz : z ∈ U)
  (h₁f₁ : MeromorphicOn f₁ U)
  (h₂f₁ : (h₁f₁ z hz).order ≠ ⊤)
  (h₁f₂ : MeromorphicOn f₂ U)
  (h₂f₂ : (h₁f₂ z hz).order ≠ ⊤) :
  (h₁f₁.mul h₁f₂).divisor.toFun z = h₁f₁.divisor.toFun z + h₁f₂.divisor.toFun z := by
  by_cases h₁z : z ∈ U
  · rw [MeromorphicOn.divisor_def₂ h₁f₁ hz h₂f₁]
    rw [MeromorphicOn.divisor_def₂ h₁f₂ hz h₂f₂]
    have B : ((h₁f₁.mul h₁f₂) z hz).order ≠ ⊤ := by
      rw [MeromorphicAt.order_mul (h₁f₁ z hz) (h₁f₂ z hz)]
      simp; tauto
    rw [MeromorphicOn.divisor_def₂ (h₁f₁.mul h₁f₂) hz B]
    simp_rw [MeromorphicAt.order_mul (h₁f₁ z hz) (h₁f₂ z hz)]
    rw [untop_add]
  · unfold MeromorphicOn.divisor
    simp [h₁z]


theorem MeromorphicOn.divisor_mul [CompleteSpace 𝕜]
  {f₁ f₂ : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁f₁ : MeromorphicOn f₁ U)
  (h₂f₁ : ∀ z, (hz : z ∈ U) → (h₁f₁ z hz).order ≠ ⊤)
  (h₁f₂ : MeromorphicOn f₂ U)
  (h₂f₂ : ∀ z, (hz : z ∈ U) → (h₁f₂ z hz).order ≠ ⊤) :
  (h₁f₁.mul h₁f₂).divisor.toFun = h₁f₁.divisor.toFun + h₁f₂.divisor.toFun := by
  funext z
  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_mul₀ hz h₁f₁ (h₂f₁ z hz) h₁f₂ (h₂f₂ z hz)]
    simp
  · simp
    rw [Function.nmem_support.mp (fun a => hz (h₁f₁.divisor.supportWithinDomain a))]
    rw [Function.nmem_support.mp (fun a => hz (h₁f₂.divisor.supportWithinDomain a))]
    rw [Function.nmem_support.mp (fun a => hz ((h₁f₁.mul h₁f₂).divisor.supportWithinDomain a))]
    simp


theorem MeromorphicOn.divisor_inv [CompleteSpace 𝕜]
  {f: 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁f : MeromorphicOn f U) :
  h₁f.inv.divisor.toFun = -h₁f.divisor.toFun := by
  funext z

  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_def₁]
    simp
    rw [MeromorphicOn.divisor_def₁]
    rw [MeromorphicAt.order_inv]
    simp
    by_cases h₂f : (h₁f z hz).order = ⊤
    · simp [h₂f]
    · let A := untop'_of_ne_top (d := 0) h₂f
      rw [← A]
      exact rfl
    repeat exact hz
  · unfold MeromorphicOn.divisor
    simp [hz]


theorem MeromorphicOn.divisor_add_const₁  [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (a : 𝕜) :
  0 ≤ hf.divisor z → 0 ≤ (hf.add (MeromorphicOn.const a)).divisor z := by
  intro h

  unfold MeromorphicOn.divisor

  -- Trivial case: z ∉ U
  by_cases hz : z ∉ U
  · simp [hz]

  -- Non-trivial case: z ∈ U
  simp at hz; simp [hz]

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
      unfold MeromorphicOn.divisor at h
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
      unfold MeromorphicOn.divisor
      simp [hz]
    rw [this] at h
    tauto

  simp at hz
  unfold MeromorphicOn.divisor
  simp [hz]
  unfold MeromorphicOn.divisor at h
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
      unfold MeromorphicOn.divisor
      simp [hz]
    rw [this] at h
    tauto

  simp at hz
  unfold MeromorphicOn.divisor
  simp [hz]
  unfold MeromorphicOn.divisor at h
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
  rw [this]


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
  unfold MeromorphicOn.divisor at A
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
    unfold MeromorphicOn.divisor
    simp [h₁f.order_ne_top hU h₂f ⟨u, hu.1⟩]
    use hu.1
    rw [(h₁f u hu.1).order_eq_zero_iff]
    simp
    exact hu.2
  · intro hu
    simp at hu
    let A := h₁f.meromorphicOn.divisor.supportWithinDomain hu
    constructor
    · exact h₁f.meromorphicOn.divisor.supportWithinDomain hu
    · simp
      let B := (h₁f u A).order_eq_zero_iff.not
      simp at B
      rw [← B]
      unfold MeromorphicOn.divisor at hu
      simp [A] at hu
      exact hu.1
