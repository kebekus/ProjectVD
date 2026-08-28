/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.NormalForm
import VD.Manifold.RiemannSphere.Manifold

/-!
# Meromorphic Functions as Holomorphic Maps to the Riemann Sphere

A meromorphic function `f : ℂ → ℂ` extends to a holomorphic map `toRiemannSphere f : ℂ → OnePoint ℂ`
into the Riemann sphere: at points where the order of `f` is non-negative, the value is the value
of the normal form `toMeromorphicNFOn f univ` of `f` (which agrees with `f` away from a discrete
set, and removes the junk values that `f` may take at removable singularities); at poles, the value
is `∞`.

## Main results

- `Meromorphic.contMDiff_toRiemannSphere`: the extension is holomorphic.
- `Meromorphic.toRiemannSphere_eventuallyEq_coe`: the extension agrees with `(↑) ∘ f` away from a
  discrete set.
-/

open Filter Function OnePoint Set Topology
open scoped Manifold

/-- The smoothness exponent `ω` of analytic maps; see `VD/Manifold/RiemannSphere/Manifold.lean`
for why the scope `ContDiff` is not opened. -/
local notation "ω" => (⊤ : WithTop ℕ∞)

variable {f : ℂ → ℂ} {z : ℂ}

/-- The extension of a meromorphic function `f : ℂ → ℂ` to a map into the Riemann sphere: the
value of the normal form of `f` where the order of `f` is non-negative, and `∞` at poles. -/
noncomputable def toRiemannSphere (f : ℂ → ℂ) (z : ℂ) : OnePoint ℂ :=
  if 0 ≤ meromorphicOrderAt f z then ((toMeromorphicNFOn f univ z : ℂ) : OnePoint ℂ) else ∞

theorem toRiemannSphere_apply_of_nonneg (h : 0 ≤ meromorphicOrderAt f z) :
    toRiemannSphere f z = ((toMeromorphicNFOn f univ z : ℂ) : OnePoint ℂ) := by
  simp [toRiemannSphere, h]

theorem toRiemannSphere_apply_of_neg (h : meromorphicOrderAt f z < 0) :
    toRiemannSphere f z = ∞ := by
  simp [toRiemannSphere, not_le.2 h]

theorem toRiemannSphere_eq_infty_iff : toRiemannSphere f z = ∞ ↔ meromorphicOrderAt f z < 0 := by
  by_cases h : 0 ≤ meromorphicOrderAt f z
  · simp [toRiemannSphere_apply_of_nonneg h, not_lt.2 h]
  · simp [toRiemannSphere_apply_of_neg (not_le.1 h), not_le.1 h]

/-- Away from a discrete set, the extension of a meromorphic function to the Riemann sphere is the
function itself. -/
theorem Meromorphic.toRiemannSphere_eventuallyEq_coe (hf : Meromorphic f) :
    toRiemannSphere f =ᶠ[codiscrete ℂ] fun z ↦ (f z : OnePoint ℂ) := by
  rw [EventuallyEq, eventually_codiscrete_iff_forall_eventually_nhdsNE]
  intro z
  filter_upwards [(hf z).eventually_analyticAt,
    (meromorphicOn_univ.2 hf).toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)] with w hw hw'
  rw [toRiemannSphere_apply_of_nonneg
    (hw.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.2 hw), hw']

/-- The extension of a meromorphic function to the Riemann sphere is holomorphic. -/
theorem Meromorphic.contMDiff_toRiemannSphere (hf : Meromorphic f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toRiemannSphere f) := by
  intro z₀
  have hfU : MeromorphicOn f univ := meromorphicOn_univ.2 hf
  set F := toMeromorphicNFOn f univ with hF_def
  have hF : ∀ z, MeromorphicNFAt F z :=
    fun z ↦ meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ z)
  have hord : ∀ z, meromorphicOrderAt F z = meromorphicOrderAt f z :=
    fun z ↦ meromorphicOrderAt_toMeromorphicNFOn hfU (mem_univ z)
  by_cases h₀ : 0 ≤ meromorphicOrderAt f z₀
  · -- Case 1: `f` has no pole at `z₀`, and `toRiemannSphere f = (↑) ∘ F` near `z₀`
    have hFa : AnalyticAt ℂ F z₀ :=
      (hF z₀).meromorphicOrderAt_nonneg_iff_analyticAt.1 (hord z₀ ▸ h₀)
    have hev : toRiemannSphere f =ᶠ[𝓝 z₀] fun z ↦ (F z : OnePoint ℂ) := by
      filter_upwards [hFa.eventually_analyticAt] with z hz
      exact toRiemannSphere_apply_of_nonneg
        (hord z ▸ (hF z).meromorphicOrderAt_nonneg_iff_analyticAt.2 hz)
    exact (OnePoint.contMDiffAt_coe_comp_iff.2 hFa.contDiffAt.contMDiffAt).congr_of_eventuallyEq hev
  · -- Case 2: `f` has a pole at `z₀`, and `toRiemannSphere f = inv ∘ (↑) ∘ F⁻¹` near `z₀`
    rw [not_le] at h₀
    have hGa : AnalyticAt ℂ F⁻¹ z₀ := by
      apply (hF z₀).inv.meromorphicOrderAt_nonneg_iff_analyticAt.1
      rw [meromorphicOrderAt_inv, hord]
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt h₀)
      have h₀' := h₀
      rw [← hn] at h₀' ⊢
      norm_cast at h₀' ⊢
      omega
    have hF₀ : F z₀ = 0 := by
      rcases meromorphicNFAt_iff_analyticAt_or.1 (hF z₀) with h | ⟨_, _, h⟩
      · exfalso
        have := (hF z₀).meromorphicOrderAt_nonneg_iff_analyticAt.2 h
        rw [hord] at this
        exact absurd h₀ (not_lt.2 this)
      · exact h
    -- `F⁻¹` does not vanish identically near `z₀`, as `f` does not
    have hGne : ∀ᶠ z in 𝓝[≠] z₀, F⁻¹ z ≠ 0 := by
      rcases hGa.eventually_eq_zero_or_eventually_ne_zero with h | h
      · exfalso
        have hf0 : f =ᶠ[𝓝[≠] z₀] 0 := by
          filter_upwards [h.filter_mono nhdsWithin_le_nhds,
            hfU.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z₀)] with z hz hz'
          rw [Pi.inv_apply, inv_eq_zero] at hz
          simpa [← hz'] using hz
        have := meromorphicOrderAt_eq_top_iff.2 hf0
        rw [this] at h₀
        exact not_top_lt h₀
      · exact h
    have hev : toRiemannSphere f =ᶠ[𝓝 z₀] fun z ↦ OnePoint.inv ((F⁻¹ z : ℂ) : OnePoint ℂ) := by
      rw [← nhdsNE_sup_pure z₀, EventuallyEq, eventually_sup, eventually_pure]
      constructor
      · filter_upwards [hGne, hGa.eventually_analyticAt.filter_mono nhdsWithin_le_nhds]
          with z hz hz'
        have hFa : AnalyticAt ℂ F z := by
          rw [← inv_inv F]
          exact hz'.inv hz
        rw [toRiemannSphere_apply_of_nonneg
          (hord z ▸ (hF z).meromorphicOrderAt_nonneg_iff_analyticAt.2 hFa), OnePoint.inv_coe hz]
        simp [hF_def]
      · rw [toRiemannSphere_apply_of_neg h₀, Pi.inv_apply, hF₀, inv_zero, OnePoint.inv_coe_zero]
    exact (OnePoint.contMDiff_inv.contMDiffAt.comp z₀
      (OnePoint.contMDiffAt_coe_comp_iff.2 hGa.contDiffAt.contMDiffAt)).congr_of_eventuallyEq hev
