import VD.PoissonJensen0

open Complex Filter Function MeromorphicOn Metric Real Set Classical Topology --ValueDistribution

/-!
## Additional Material
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {x : 𝕜}

@[simp] theorem meromorphicAt_fun_comp_add_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (f ∘ fun z ↦ (z + c)) (x - c) ↔ MeromorphicAt f x := by
  constructor
  · intro h
    convert h.comp_analyticAt (g := fun z ↦ z - c) (by fun_prop)
    aesop
  · intro h
    rw [(by ring : x = (x - c) + c)] at h
    exact h.comp_analyticAt (g := fun z ↦ z + c) (by fun_prop)

@[simp] theorem meromorphicAt_comp_add_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (fun z ↦ f (z + c)) (x - c) ↔ MeromorphicAt f x :=
  meromorphicAt_fun_comp_add_const_iff_meromorphicAt

@[simp] theorem meromorphicAt_fun_comp_sub_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (f ∘ fun z ↦ (z - c)) (x + c) ↔ MeromorphicAt f x := by
  simp [← meromorphicAt_fun_comp_add_const_iff_meromorphicAt (f := f) (c := -c), sub_eq_add_neg]

@[simp] theorem meromorphicAt_comp_sub_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (fun z ↦ f (z - c)) (x + c) ↔ MeromorphicAt f x :=
  meromorphicAt_fun_comp_sub_const_iff_meromorphicAt

@[simp] theorem meromorphicOn_fun_comp_add_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} {f : 𝕜 → E} :
    MeromorphicOn (f ∘ fun z ↦ (z + c)) {x | x + c ∈ U} ↔ MeromorphicOn f U := by
  constructor
  · intro h y hy
    rw [← meromorphicAt_fun_comp_add_const_iff_meromorphicAt (c := c)]
    apply h
    aesop
  · intro h y hy
    rw [← meromorphicAt_fun_comp_sub_const_iff_meromorphicAt (c := c),
      (by aesop : ((f ∘ fun z ↦ z + c) ∘ fun z ↦ z - c) = f)]
    exact h (y + c) (mem_preimage.mp hy)

/-!
## Formula goes here
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {x c w : ℂ} {f h : ℂ → ℂ}


theorem poissonJensen {c : ℂ}
    (h₁w : w ∈ ball c R)
    (h₃w : meromorphicOrderAt f w = 0)
    (h₁f : MeromorphicOn f (closedBall c R))
    (h₂f : ∀ u : (closedBall (c : ℂ) R), meromorphicOrderAt f u ≠ ⊤) -- can be deduced
    (hR : 0 < R) : -- can be decuced
    Real.log ‖meromorphicTrailingCoeffAt f w‖
      = circleAverage (re ∘ herglotzRieszKernel c w * (Real.log ‖f ·‖)) c R
        - ∑ᶠ i, (divisor f (ball c R) i) * Real.log ‖canonicalFactor R i (w - c)‖ := by
  let g := fun z ↦ f (z + c)
  have : f = fun z ↦ g (z - c) := by simp [g]
  repeat rw [this]
  simp
  have : meromorphicTrailingCoeffAt (fun z ↦ g (z - c)) w = meromorphicTrailingCoeffAt g (w - c) := by
    sorry
  rw [this]
  rw [poissonJensen₀ (R := R)]
  congr 1
  · simp only [← Real.circleAverage_map_add_const (c := c), Pi.mul_apply, comp_apply,
      add_sub_cancel_right]
    congr
    ext x
    exact (herglotzRieszKernel_add_const c w x).symm
  · apply finsum_congr
    intro x
    congr 2
    -- should be simp
    rw [divisor_def, divisor_def]
    grind
    sorry
  · sorry
  · sorry
  · sorry
