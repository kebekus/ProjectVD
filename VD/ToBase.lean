/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.Divisor.Basic
import VD.stronglyMeromorphicOn
import VD.ToMathlib.meromorphicOn_levelSetOfOrder

open Classical

variable
  {α : Type*} [Zero α]

noncomputable def WithTop.toBase (a : WithTop α) : α := a.untopD 0

lemma WithTop.toBase_def (a : WithTop α) :
    a.toBase = a.untopD 0 := rfl

@[simp]
lemma WithTop.toBase_eq_zero_iff (a : WithTop α) :
    a.toBase = 0 ↔ a = 0 ∨ a = ⊤ := by simp_all [WithTop.toBase_def]

--@[simp] lemma WithTop.toBase_of_zero : (0 : WithTop α).toBase = 0 := rfl

@[simp] lemma WithTop.toBase_coe (a : α) : (a : WithTop α).toBase = a := rfl
