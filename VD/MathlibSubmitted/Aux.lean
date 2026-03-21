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

/-
@[simp] theorem MultlinearMap.map_zero {n : ℕ} (D : E [×n]→L[𝕜] F) (hn : 0 < n) :
    D 0 = 0 := D.map_coord_zero ⟨0, hn⟩ rfl

@[simp] theorem ContinuousMultlinearMap.map_zero {n : ℕ} (D : E [×n]→L[𝕜] F) (hn : 0 < n) :
    D 0 = 0 := D.map_coord_zero ⟨0, hn⟩ rfl
-/
