/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, based on code by Yury Kudryashov
-/
--module

--public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import VD.MathlibSubmitted.IteratedFDeriv

/-!
# Functions Harmonic on a Domain and Continuous on Its Closure

Many theorems in harmonic analysis assume that a function is complex harmonic on
a domain and is continuous on its closure. In this file we define a predicate
`HarmonicContOnCl` that expresses this property and prove basic facts about this
predicate.
-/

@[expose] public section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f f₁ f₂ : E → F}
  {x : E} {s : Set E} {c : ℝ}

open Laplacian Metric Topology

namespace InnerProductSpace

/-!
# ELSEWHERE
-/

theorem _root_.ContDiffAt.laplacian_sub (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ - f₂) x = Δ f₁ x - Δ f₂ x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_sub_distrib, iteratedFDeriv_sub_apply h₁ h₂]

theorem _root_.ContDiffAt.laplacian_sub_nhds (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ - f₂) =ᶠ[𝓝 x] (Δ f₁) - (Δ f₂) := by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplacian_sub h₂x

theorem HarmonicAt.sub (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x) :
    HarmonicAt (f₁ - f₂) x := by
  constructor
  · exact h₁.1.sub h₂.1
  · filter_upwards [h₁.1.laplacian_sub_nhds h₂.1, h₁.2, h₂.2]
    simp_all

theorem HarmonicOnNhd.sub (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s) :
    HarmonicOnNhd (f₁ - f₂) s := fun x hx ↦ (h₁ x hx).sub (h₂ x hx)

@[fun_prop] theorem HarmonicOnNhd.continuousOn (h : HarmonicOnNhd f s) :
    ContinuousOn f s :=
  fun x hx ↦ (h x hx).1.continuousAt.continuousWithinAt (s := s)

@[simp] theorem laplacian_const {c : F} :
    Laplacian.laplacian (fun (_ : E) ↦ c) = 0 := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_of_ne two_ne_zero,
    Pi.zero_def]

@[simp] theorem harmonicOnAt_const (c : F) :
    HarmonicAt (fun _ ↦ c) x := ⟨by fun_prop, by simp⟩

@[simp] theorem harmonicOnNhd_const (c : F) :
    HarmonicOnNhd (fun _ ↦ c) s := fun _ _ ↦ by simp

theorem laplacian_neg :
    Δ (-f) = -(Δ f) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_neg]
  aesop

theorem HarmonicAt.neg (h : HarmonicAt f x) :
    HarmonicAt (-f) x := by
  constructor
  · simpa using h.1.neg
  · filter_upwards [h.2] with x hx
    simp_all [laplacian_neg]

theorem HarmonicOnNhd.neg (h : HarmonicOnNhd f s) :
    HarmonicOnNhd (-f) s := fun x hx ↦ (h x hx).neg

/-!
# END ELSEWHERE
-/

/--
A predicate saying that a function is harmonic on a set and is continuous on its
closure. This is a common assumption in harmonic analysis.
-/
@[fun_prop] structure HarmonicContOnCl (f : E → F) (s : Set E) : Prop where
  protected harmonicOnNhd : HarmonicOnNhd f s
  protected continuousOn : ContinuousOn f (closure s)

@[fun_prop] theorem HarmonicOnNhd.harmonicContOnCl (h : HarmonicOnNhd f (closure s)) :
    HarmonicContOnCl f s :=
  ⟨h.mono subset_closure, h.continuousOn⟩

theorem IsClosed.harmonicContOnCl_iff (hs : IsClosed s) :
    HarmonicContOnCl f s ↔ HarmonicOnNhd f s where
  mp := (·.1 · ·)
  mpr h := by
    rw [← hs.closure_eq] at h
    exact h.harmonicContOnCl

@[fun_prop] theorem harmonicContOnCl_const {c : F} : HarmonicContOnCl (fun _ : E ↦ c) s :=
  ⟨harmonicOnNhd_const c, continuousOn_const⟩

namespace HarmonicContOnCl

theorem continuousOn_ball [NormedSpace ℝ E] {x : E} {r : ℝ} (h : HarmonicContOnCl f (ball x r)) :
    ContinuousOn f (closedBall x r) := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero]
    exact continuousOn_singleton f x
  · rw [← closure_ball x hr]
    exact h.continuousOn

theorem mk_ball {x : E} {r : ℝ} (hd : HarmonicOnNhd f (ball x r))
    (hc : ContinuousOn f (closedBall x r)) :
    HarmonicContOnCl f (ball x r) :=
  ⟨hd, hc.mono <| closure_ball_subset_closedBall⟩

@[fun_prop] theorem contDiffAt (h : HarmonicContOnCl f s) (hx : x ∈ s) :
    ContDiffAt ℝ 2 f x := (h.1 x hx).1

@[fun_prop] theorem differentiableAt (h : HarmonicContOnCl f s) (hx : x ∈ s) :
    DifferentiableAt ℝ f x := (h.contDiffAt hx).differentiableAt two_ne_zero

@[fun_prop] theorem mono (h : HarmonicContOnCl f s) (ht : t ⊆ s) :
    HarmonicContOnCl f t := ⟨h.harmonicOnNhd.mono ht, h.continuousOn.mono (closure_mono ht)⟩

@[fun_prop] theorem add (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s) :
    HarmonicContOnCl (f₁ + f₂) s := ⟨hf₁.1.add hf₂.1, hf₁.2.add hf₂.2⟩

@[fun_prop] theorem fun_add (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s) :
    HarmonicContOnCl (fun x ↦ f₁ x + f₂ x) s := hf₁.add hf₂

@[fun_prop] theorem add_const (hf : HarmonicContOnCl f s) (c : F) :
    HarmonicContOnCl (f + fun _ ↦ c) s := hf.add harmonicContOnCl_const

@[fun_prop] theorem fun_add_const (hf : HarmonicContOnCl f s) (c : F) :
    HarmonicContOnCl (fun x ↦ f x + c) s := hf.add harmonicContOnCl_const

@[fun_prop] theorem const_add (hf : HarmonicContOnCl  f s) (c : F) :
  HarmonicContOnCl ((fun _ ↦ c) + f) s := harmonicContOnCl_const.add hf

@[fun_prop] theorem fun_const_add (hf : HarmonicContOnCl  f s) (c : F) :
  HarmonicContOnCl (fun x ↦ c + f x) s := harmonicContOnCl_const.add hf

@[fun_prop] theorem neg (hf : HarmonicContOnCl  f s) :
    HarmonicContOnCl  (-f) s := ⟨hf.1.neg, hf.2.neg⟩

@[fun_prop] theorem fun_neg (hf : HarmonicContOnCl  f s) :
    HarmonicContOnCl  (fun x ↦ -f x) s := ⟨hf.1.neg, hf.2.neg⟩

@[fun_prop] theorem sub (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s) :
    HarmonicContOnCl (f₁ - f₂) s := ⟨hf₁.1.sub hf₂.1, hf₁.2.sub hf₂.2⟩

@[fun_prop] theorem fun_sub (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s) :
    HarmonicContOnCl (fun x ↦ f₁ x - f₂ x) s := ⟨hf₁.1.sub hf₂.1, hf₁.2.sub hf₂.2⟩

@[fun_prop] theorem sub_const (hf : HarmonicContOnCl  f s) (c : F) :
    HarmonicContOnCl (f - fun _ ↦ c) s := hf.sub harmonicContOnCl_const

@[fun_prop] theorem fun_sub_const (hf : HarmonicContOnCl  f s) (c : F) :
    HarmonicContOnCl (fun x ↦ f x - c) s := hf.sub harmonicContOnCl_const

@[fun_prop] theorem const_sub (hf : HarmonicContOnCl  f s) (c : F) :
    HarmonicContOnCl ((fun _ ↦ c) - f) s := harmonicContOnCl_const.sub hf

@[fun_prop] theorem fun_const_sub (hf : HarmonicContOnCl  f s) (c : F) :
    HarmonicContOnCl  (fun x ↦ c - f x) s := harmonicContOnCl_const.sub hf

@[fun_prop] theorem const_smul (hf : HarmonicContOnCl f s) (c : ℝ) :
    HarmonicContOnCl (c • f) s := ⟨hf.1.const_smul, hf.2.const_smul c⟩

@[fun_prop] theorem fun_const_smul (hf : HarmonicContOnCl f s) (c : ℝ) :
    HarmonicContOnCl (c • f) s := ⟨hf.1.const_smul, hf.2.const_smul c⟩

end HarmonicContOnCl

end InnerProductSpace
