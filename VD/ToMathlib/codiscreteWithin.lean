import Mathlib.Topology.DiscreteSubset

open Filter Set Topology

variable {X : Type*} [TopologicalSpace X] {U s : Set X}

/-- Codiscreteness within `U` depends only on the intersection with `U`. -/
theorem codiscreteWithin_congr_inter
    {X : Type u_1} [TopologicalSpace X]
    {S₁ S₂ U : Set X}
    (hST : S₁ ∩ U = S₂ ∩ U) :
    S₁ ∈ Filter.codiscreteWithin U ↔ S₂ ∈ Filter.codiscreteWithin U := by
  rw [mem_codiscreteWithin, mem_codiscreteWithin, ← Set.diff_inter_self_eq_diff, hST,
    Set.diff_inter_self_eq_diff]
