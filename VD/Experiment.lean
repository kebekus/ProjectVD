import Mathlib

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution

lemma div_self_ne_one : (fun x ↦ x) / (fun x ↦ x) ≠ (1 : ℂ → ℂ) := by
  rw [ne_iff]
  use 0
  simp
