/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Order

/-!
# Analytic Extensions and Non-Negative Meromorphic Order

A meromorphic function has non-negative order at a point if and only if it admits an analytic
extension across that point. The analogous *continuous*-extension characterization is already in
Mathlib as `tendsto_nhds_iff_meromorphicOrderAt_nonneg`, together with the removable-singularity
result `MeromorphicAt.analyticAt`.

The analytic-extension characterization `MeromorphicAt.order_nonneg_iff_exists_analytic_extension`
is not yet in Mathlib and could be upstreamed to `Mathlib/Analysis/Meromorphic/Order.lean`.
-/

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {z₀ : 𝕜}

/-- If a meromorphic function has non-negative order then there exists an analytic extension. -/
theorem MeromorphicAt.exists_analytic_extension_if_order_nonneg (hf : MeromorphicAt f z₀)
    (nneg : 0 ≤ meromorphicOrderAt f z₀) :
    ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
  by_cases h' : meromorphicOrderAt f z₀ = ⊤
  · use 0
    exact ⟨analyticAt_const, meromorphicOrderAt_eq_top_iff.mp h'⟩
  · let n := (meromorphicOrderAt f z₀).untop (LT.lt.ne_top (WithTop.lt_top_iff_ne_top.mpr h'))
    have h₀ : meromorphicOrderAt f z₀ = n := by simp [n]
    obtain ⟨g, hg, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp h₀
    use (fun z ↦ (z - z₀) ^ n • g z)
    constructor
    · apply AnalyticAt.smul _ hg
      · simp only [h₀, WithTop.coe_nonneg] at nneg
        obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le nneg
        simp only [ha, zpow_natCast]
        apply (analyticAt_id.sub analyticAt_const).pow
    · exact hfg.2

/-- A meromorphic function has non-negative order iff there exists an analytic extension. -/
theorem MeromorphicAt.order_nonneg_iff_exists_analytic_extension (hf : MeromorphicAt f z₀) :
    0 ≤ meromorphicOrderAt f z₀ ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
  refine ⟨hf.exists_analytic_extension_if_order_nonneg, ?_⟩
  rintro ⟨g, hg₁, hg₂⟩
  rw [meromorphicOrderAt_congr hg₂]
  exact hg₁.meromorphicOrderAt_nonneg
