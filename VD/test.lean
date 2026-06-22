import Mathlib

variable {X : Type*} {G : Set (Set X)}

theorem uniqueness_of_lines :
    ∀ x y : X, ∃ g ∈ G, x ≠ y → (x ∈ g ∧ y ∈ g) := by
  sorry
