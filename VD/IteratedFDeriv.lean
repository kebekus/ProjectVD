/-
Copyright (c) 2022 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, based on code by Yury Kudryashov
-/

import Mathlib.Analysis.Calculus.ContDiff.Operations


open Set NNReal Nat ContDiff Topology

open Set Fin Filter Function


/-!
# ELSEWHERE
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {s : Set E} {x : E} {i : ℕ} {f g : E → F}

theorem iteratedFDerivWithin_sub_apply {f g : E → F} (hf : ContDiffWithinAt 𝕜 i f s x)
    (hg : ContDiffWithinAt 𝕜 i g s x) (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (f - g) s x =
      iteratedFDerivWithin 𝕜 i f s x - iteratedFDerivWithin 𝕜 i g s x := by
  rw [sub_eq_add_neg, iteratedFDerivWithin_add_apply hf _ hu hx,
    iteratedFDerivWithin_neg_apply hu hx, sub_eq_add_neg]
  exact hg.neg

theorem iteratedFDerivWithin_fun_sub_apply {f g : E → F} (hf : ContDiffWithinAt 𝕜 i f s x)
    (hg : ContDiffWithinAt 𝕜 i g s x) (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (fun x ↦ f x - g x) s x =
      iteratedFDerivWithin 𝕜 i f s x - iteratedFDerivWithin 𝕜 i g s x :=
  iteratedFDerivWithin_sub_apply hf hg hu hx

theorem iteratedFDeriv_sub_apply {i : ℕ} {f g : E → F}
    (hf : ContDiffAt 𝕜 i f x) (hg : ContDiffAt 𝕜 i g x) :
    iteratedFDeriv 𝕜 i (f - g) x = iteratedFDeriv 𝕜 i f x - iteratedFDeriv 𝕜 i g x := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_sub_apply hf hg uniqueDiffOn_univ (Set.mem_univ _)

theorem iteratedFDeriv_fun_sub_apply {i : ℕ} {f g : E → F} (hf : ContDiffAt 𝕜 i f x)
    (hg : ContDiffAt 𝕜 i g x) :
    iteratedFDeriv 𝕜 i (fun x => f x - g x) x = iteratedFDeriv 𝕜 i f x - iteratedFDeriv 𝕜 i g x :=
  iteratedFDeriv_sub_apply hf hg

theorem iteratedFDeriv_sub {i : ℕ} {f g : E → F} (hf : ContDiff 𝕜 i f) (hg : ContDiff 𝕜 i g) :
    iteratedFDeriv 𝕜 i (f - g) = iteratedFDeriv 𝕜 i f - iteratedFDeriv 𝕜 i g :=
  funext fun _ ↦ iteratedFDeriv_sub_apply (ContDiff.contDiffAt hf) (ContDiff.contDiffAt hg)

theorem iteratedFDeriv_fun_sub {i : ℕ} {f g : E → F} (hf : ContDiff 𝕜 i f) (hg : ContDiff 𝕜 i g) :
    iteratedFDeriv 𝕜 i (fun x ↦ f x - g x) = iteratedFDeriv 𝕜 i f - iteratedFDeriv 𝕜 i g :=
  funext fun _ ↦ iteratedFDeriv_sub_apply (ContDiff.contDiffAt hf) (ContDiff.contDiffAt hg)
