import Mathlib.Analysis.Complex.MeanValue

open Asymptotics Classical Complex ComplexConjugate Filter Function Metric Real Set Classical Topology

theorem IntervalIntegrable.comp_add_right_iff
    {ε : Type u_3} [TopologicalSpace ε] [ENormedAddMonoid ε]
    {f : ℝ → ε} {a b : ℝ} [TopologicalSpace.PseudoMetrizableSpace ε]
    {c : ℝ}
    (h : ‖f (min a b)‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (x + c)) MeasureTheory.volume (a - c) (b - c)
      ↔ IntervalIntegrable f MeasureTheory.volume a b :=
  ⟨fun hf ↦ by simpa using hf.comp_add_right (-c) (by simp_all [min_add]),
    (·.comp_add_right c)⟩

theorem IntervalIntegrable.comp_add_left_iff
    {ε : Type u_3} [TopologicalSpace ε] [ENormedAddMonoid ε]
    {f : ℝ → ε} {a b : ℝ} [TopologicalSpace.PseudoMetrizableSpace ε]
    {c : ℝ}
    (h : ‖f (min a b)‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (c + x)) MeasureTheory.volume (a - c) (b - c)
      ↔ IntervalIntegrable f MeasureTheory.volume a b := by
  simp_rw [add_comm c, IntervalIntegrable.comp_add_right_iff h]

theorem IntervalIntegrable.comp_sub_right_iff
    {ε : Type u_3} [TopologicalSpace ε] [ENormedAddMonoid ε]
    {f : ℝ → ε} {a b : ℝ} [TopologicalSpace.PseudoMetrizableSpace ε]
    {c : ℝ}
    (h : ‖f (min a b)‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun x ↦ f (x - c)) MeasureTheory.volume (a + c) (b + c)
      ↔ IntervalIntegrable f MeasureTheory.volume a b := by
  simp_rw [sub_eq_add_neg, ← IntervalIntegrable.comp_add_right_iff h (c := -c), sub_neg_eq_add]

theorem Function.Periodic.intervalIntegrable_iff
    {E : Type u_1} [NormedAddCommGroup E]
    {f : ℝ → E} {T t₁ t₂ : ℝ} (hf : Periodic f T) (hT : 0 < T)
    (h₁ : ‖f (min t₁ (t₁ + T))‖ₑ ≠ ⊤ := by finiteness)
    (h₂ : ‖f (min t₂ (t₂ + T))‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable f MeasureTheory.volume t₁ (t₁ + T)
      ↔ IntervalIntegrable f MeasureTheory.volume t₂ (t₂ + T) :=
  ⟨(hf.intervalIntegrable hT h₁ · t₂ (t₂ + T)), (hf.intervalIntegrable hT h₂ · t₁ (t₁ + T))⟩


variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}

omit [NormedSpace ℂ E] in
theorem CircleIntegrable.congr {f₁ f₂ : ℂ → E}
    (hf : Set.EqOn f₁ f₂ (Metric.sphere c |R|)) :
    CircleIntegrable f₁ c R ↔ CircleIntegrable f₂ c R :=
  intervalIntegrable_congr (fun x _ ↦ hf (circleMap_mem_sphere' c R x))

omit [NormedSpace ℂ E] in
theorem circleIntegrable_congr_neg_radius :
    CircleIntegrable f c R ↔ CircleIntegrable f c (-R) := by
  unfold CircleIntegrable
  rw [intervalIntegrable_congr (f := fun θ ↦ f (circleMap c (-R) θ))
    (g := fun θ ↦ f (circleMap c R (θ + π))) (fun _ _ ↦ by simp [circleMap_neg_radius]),
    ← IntervalIntegrable.comp_add_right_iff (c := π)]
  have a₀ : (fun x ↦ f (circleMap c R (x + π))).Periodic (2 * π) := by
    intro x
    simp only [circleMap, ofReal_add, ofReal_mul, ofReal_ofNat]
    congr 3
    rw [exp_eq_exp_iff_exists_int]
    use 1
    ring
  simpa [(by ring : (2 * π - π) = (-π + 2 * π))] using
    a₀.intervalIntegrable_iff two_pi_pos (t₁ := -π) (t₂ := 0)
