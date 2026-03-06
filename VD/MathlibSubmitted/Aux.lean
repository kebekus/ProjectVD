/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Topology

set_option backward.isDefEq.respectTransparency false

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {e : E} {s : Set E} {f₁ f₂ : E → F}

noncomputable section

@[to_fun (attr := simp)] lemma iteratedFDeriv_zero_fun' {n : ℕ} :
    iteratedFDeriv 𝕜 n (0 : E → F) = 0 :=
  iteratedFDeriv_zero_fun

@[to_fun (attr := simp)] lemma iteratedFDerivWithin_zero_fun' {n : ℕ} :
    iteratedFDerivWithin 𝕜 n (0 : E → F) s = 0 :=
  iteratedFDerivWithin_zero_fun

@[to_fun (attr := simp)] lemma ftaylorSeriesWithin_zero_fun :
    ftaylorSeriesWithin 𝕜 (0 : E → F) = 0 := by
  ext
  simp [ftaylorSeriesWithin]

@[to_fun (attr := simp)] lemma ftaylorSeries_zero_fun :
    ftaylorSeries 𝕜 (0 : E → F) = 0 := by
  ext
  simp [ftaylorSeries]

--

@[to_fun] theorem iteratedFDerivWithin_sum_apply' {ι : Type*} {f : ι → E → F} {u : Finset ι} {n : ℕ}
    (h : ∀ j ∈ u, ContDiffWithinAt 𝕜 n (f j) s e) (hs : UniqueDiffOn 𝕜 s) (he : e ∈ s):
    iteratedFDerivWithin 𝕜 n (∑ j ∈ u, f j) s e = ∑ j ∈ u, iteratedFDerivWithin 𝕜 n (f j) s e := by
  simpa [(by aesop : (∑ j ∈ u, f j) = (fun x ↦ ∑ j ∈ u, f j x))]
    using iteratedFDerivWithin_sum_apply hs he h

@[to_fun] theorem iteratedFDeriv_sum_apply {ι : Type*} {f : ι → E → F} {u : Finset ι} {n : ℕ}
    (h : ∀ j ∈ u, ContDiffAt 𝕜 n (f j) e) :
    iteratedFDeriv 𝕜 n (∑ j ∈ u, f j) e = ∑ j ∈ u, iteratedFDeriv 𝕜 n (f j) e := by
  simp [← iteratedFDerivWithin_univ]
  apply iteratedFDerivWithin_sum_apply' h uniqueDiffOn_univ (Set.mem_univ e)

variable (𝕜) in
lemma Filter.EventuallyEq.ftaylorSeries (h : f₁ =ᶠ[𝓝 e] f₂) :
    ftaylorSeries 𝕜 f₁ =ᶠ[𝓝 e] ftaylorSeries 𝕜 f₂ := by
  filter_upwards [eventually_eventuallyEq_nhds.2 h] with e₁ he₁
  ext n : 1
  exact (Filter.EventuallyEq.iteratedFDeriv 𝕜 he₁ n).eq_of_nhds

variable (𝕜) in
lemma Filter.EventuallyEq.ftaylorSeriesWithin (h : f₁ =ᶠ[𝓝[s] e] f₂) :
    ftaylorSeriesWithin 𝕜 f₁ s =ᶠ[𝓝[s] e] ftaylorSeriesWithin 𝕜 f₂ s := by
  filter_upwards [eventually_eventually_nhdsWithin.2 h, self_mem_nhdsWithin] with e₁ h₁e₁ h₂e₁
  ext n : 1
  apply (Filter.EventuallyEq.iteratedFDerivWithin (𝕜 := 𝕜) h₁e₁ n).eq_of_nhdsWithin h₂e₁

--@[simp] theorem MultlinearMap.map_zero {n : ℕ} (D : E [×n]→ₗ[𝕜] F) (hn : 0 < n) :
--    D 0 = 0 := D.map_coord_zero ⟨0, hn⟩ rfl

@[simp] theorem ContinuousMultlinearMap.map_zero {n : ℕ} (D : E [×n]→L[𝕜] F) (hn : 0 < n) :
    D 0 = 0 := D.map_coord_zero ⟨0, hn⟩ rfl
