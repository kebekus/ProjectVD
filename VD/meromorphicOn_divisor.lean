import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Meromorphic.Divisor.Basic
import VD.mathlibAddOn
import VD.meromorphicOn
import VD.stronglyMeromorphicOn
import Mathlib.Analysis.Meromorphic.Divisor.MeromorphicFunction

open scoped Interval Topology
open Classical
open Real Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]


theorem MeromorphicOn.divisor_add_const₁  [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (a : 𝕜) :
--  0 ≤ divisor f hf z → 0 ≤ divisor (f + fun _ ↦ a) (hf.add (MeromorphicOn.const a)) z := by
  0 ≤ divisor f U z → 0 ≤ divisor (f + fun _ ↦ a) U z := by
  intro h

  -- Trivial case: z ∉ U
  by_cases hz : z ∉ U
  · simp [hz]

  -- Non-trivial case: z ∈ U
  simp at hz
  simp [hf.add (MeromorphicOn.const a), hz]

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
      have := h
      simp [hf, hz] at this
      let V := untop'_of_ne_top (d := 0) h₁f
      rw [← V]
      simpa [h]
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
  divisor f U z < 0 → divisor (f + fun _ ↦ a) U z < 0 := by
  intro h

  by_cases hz : z ∉ U
  · have : divisor f U z = 0 := by
      simp_all [hz]
    rw [this] at h
    tauto

  simp at hz
  simp_all [hf.add (MeromorphicOn.const a), hz]

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
--  divisor f hf z < 0 → divisor (f + fun _ ↦ a) (hf.add (MeromorphicOn.const a)) z = divisor f hf z := by
  divisor f U z < 0 → divisor (f + fun _ ↦ a) U z = divisor f U z := by
  intro h

  by_cases hz : z ∉ U
  · have : divisor f U z = 0 := by
      simp_all
    rw [this] at h
    tauto

  simp at hz
  simp [hf, (hf.add (MeromorphicOn.const a)), hz]

  have : (hf z hz).order = (((hf.add (MeromorphicOn.const a))) z hz).order := by
    have t₀ : (hf z hz).order < (0 : ℤ) := by
        by_contra hCon
        simp only [not_lt] at hCon
        rw [←WithTop.le_untopD_iff (b := 0)] at hCon
        simp [hf, hz] at h
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
