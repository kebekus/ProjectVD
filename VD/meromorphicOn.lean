import VD.ToMathlib.divisor
import VD.meromorphicAt
import VD.stronglyMeromorphicOn
import VD.mathlibAddOn

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → 𝕜} {z₀ : 𝕜}

theorem MeromorphicOn.nonvanish_of_order_ne_top
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁f : MeromorphicOn f U)
  (h₂f : ∃ u : U, (h₁f u u.2).order ≠ ⊤)
  (h₁U : IsConnected U)
  (h₂U : interior U ≠ ∅) :
  ∃ u ∈ U, f u ≠ 0 := by

  by_contra hCon
  push_neg at hCon

  have : ∃ u : U, (h₁f u u.2).order = ⊤ := by
    obtain ⟨v, h₁v⟩ := Set.nonempty_iff_ne_empty'.2 h₂U
    have h₂v : v ∈ U := by apply interior_subset h₁v
    use ⟨v, h₂v⟩
    rw [MeromorphicAt.order_eq_top_iff]
    rw [eventually_nhdsWithin_iff]
    rw [eventually_nhds_iff]
    use interior U
    constructor
    · intro y h₁y h₂y
      exact hCon y (interior_subset h₁y)
    · simp [h₁v]

  let A := h₁f.exists_order_ne_top_iff_forall h₁U
  rw [← not_iff_not] at A
  push_neg at A
  have B := A.2 this
  obtain ⟨u, hu⟩ := h₂f
  tauto
