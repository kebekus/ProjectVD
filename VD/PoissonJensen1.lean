import VD.PoissonJensen0

open Complex Filter Function MeromorphicOn Metric Real Set Classical Topology --ValueDistribution

/-!
## Additional Material

Partially by Aristotle AI
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {x : 𝕜}

@[simp] theorem meromorphicAt_comp_add_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (f ∘ fun z ↦ (z + c)) (x - c) ↔ MeromorphicAt f x := by
  constructor
  · intro h
    convert h.comp_analyticAt (g := fun z ↦ z - c) (by fun_prop)
    aesop
  · intro h
    rw [(by ring : x = (x - c) + c)] at h
    exact h.comp_analyticAt (g := fun z ↦ z + c) (by fun_prop)

@[simp] theorem meromorphicAt_fun_comp_add_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (fun z ↦ f (z + c)) (x - c) ↔ MeromorphicAt f x :=
  meromorphicAt_comp_add_const_iff_meromorphicAt

@[simp] theorem meromorphicAt_comp_sub_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (f ∘ fun z ↦ (z - c)) (x + c) ↔ MeromorphicAt f x := by
  simp [← meromorphicAt_fun_comp_add_const_iff_meromorphicAt (f := f) (c := -c), ← sub_eq_add_neg]
  rfl

@[simp] theorem meromorphicAt_fun_comp_sub_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (fun z ↦ f (z - c)) (x + c) ↔ MeromorphicAt f x :=
  meromorphicAt_comp_sub_const_iff_meromorphicAt

@[simp] theorem meromorphicOn_comp_add_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} {f : 𝕜 → E} :
    MeromorphicOn (f ∘ fun z ↦ (z + c)) {x | x + c ∈ U} ↔ MeromorphicOn f U := by
  constructor
  · intro h y hy
    rw [← meromorphicAt_fun_comp_add_const_iff_meromorphicAt (c := c)]
    apply h
    aesop
  · intro h y hy
    rw [← meromorphicAt_comp_sub_const_iff_meromorphicAt (c := c),
      (by aesop : ((f ∘ fun z ↦ z + c) ∘ fun z ↦ z - c) = f)]
    exact h (y + c) (mem_preimage.mp hy)

@[simp] theorem meromorphicOn_fun_comp_add_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} {f : 𝕜 → E} :
    MeromorphicOn (fun z ↦ f (z + c)) {x | x + c ∈ U} ↔ MeromorphicOn f U :=
  meromorphicOn_comp_add_const_iff_meromorphicOn

@[simp] theorem meromorphicOn_comp_sub_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} {f : 𝕜 → E} :
    MeromorphicOn (f ∘ fun z ↦ (z - c)) {x | x - c ∈ U} ↔ MeromorphicOn f U := by
  simp [← meromorphicOn_comp_add_const_iff_meromorphicOn (f := f) (c := -c), ← sub_eq_add_neg]

@[simp] theorem meromorphicOn_fun_comp_sub_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} {f : 𝕜 → E} :
    MeromorphicOn (fun z ↦ f (z - c)) {x | x - c ∈ U} ↔ MeromorphicOn f U :=
  meromorphicOn_comp_sub_const_iff_meromorphicOn

@[simp] theorem meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    MeromorphicOn (f ∘ fun z ↦ (z - c)) (Metric.ball c R) ↔ MeromorphicOn f (Metric.ball 0 R) := by
  convert meromorphicOn_comp_sub_const_iff_meromorphicOn
  ext x
  rw [mem_ball_iff_norm]
  simp

@[simp] theorem meromorphicOn_ball_fun_comp_sub_const_iff_meromorphicOn_ball {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    MeromorphicOn (fun z ↦ f (z - c)) (Metric.ball c R) ↔ MeromorphicOn f (Metric.ball 0 R) :=
  meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball

@[simp] theorem meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    MeromorphicOn (f ∘ fun z ↦ (z - c)) (Metric.closedBall c R) ↔ MeromorphicOn f (Metric.closedBall 0 R) := by
  convert meromorphicOn_comp_sub_const_iff_meromorphicOn
  ext x
  rw [mem_closedBall_iff_norm]
  simp

@[simp] theorem meromorphicOn_closedBall_fun_comp_sub_const_iff_meromorphicOn_closedBall {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    MeromorphicOn (fun z ↦ f (z - c)) (Metric.closedBall c R) ↔ MeromorphicOn f (Metric.closedBall 0 R) :=
  meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall

@[simp] theorem meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    MeromorphicOn (f ∘ fun z ↦ (z - c)) (Metric.sphere c R) ↔ MeromorphicOn f (Metric.sphere 0 R) := by
  convert meromorphicOn_comp_sub_const_iff_meromorphicOn
  ext x
  rw [mem_sphere_iff_norm]
  simp

@[simp] theorem meromorphicOn_sphere_fun_comp_sub_const_iff_meromorphicOn_sphere {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    MeromorphicOn (fun z ↦ f (z - c)) (Metric.sphere c R) ↔ MeromorphicOn f (Metric.sphere 0 R) :=
  meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere

--
@[simp] theorem analyticOrderAt_affineMonomial {z₀ : 𝕜} : analyticOrderAt (· - z₀) z₀ = 1 := by
    convert analyticOrderAt_centeredMonomial (z₀ := z₀) (n := 1) using 2
    rw [pow_one]

@[simp] theorem meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicOrderAt (f ∘ fun z ↦ (z + c)) (x - c) = meromorphicOrderAt f x := by
  by_cases h : ¬ MeromorphicAt f x
  · simp_all
  rw [MeromorphicAt.meromorphicOrderAt_comp (by simp_all) (by fun_prop)]
  · have {a b c : 𝕜} : a + b - c = a - (c - b) := by ring
    simp [this]
  · have {a b c : 𝕜} : a + b - (c - b + b) = a - (c - b) := by ring
    simp_rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, this]
    simp

@[simp] theorem meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicOrderAt (fun z ↦ f (z + c)) (x - c) = meromorphicOrderAt f x :=
  meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt

@[simp] theorem meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicOrderAt (f ∘ fun z ↦ (z - c)) (x + c) = meromorphicOrderAt f x := by
  simp [← meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (f := f) (c := -c), ← sub_eq_add_neg]

@[simp] theorem meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicOrderAt (fun z ↦ f (z - c)) (x + c) = meromorphicOrderAt f x :=
  meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → 𝕜} {x : 𝕜}

/--
If `g` is analytic at `x` and not locally constant, and `f` is meromorphic at `g
x`, then the trailing coefficient of `f ∘ g` at `x` is the trailing coefficient
of `g · - g x` raised to the meromorphic order of `f` at `g x`, and smul'd with
the trailing coefficient of `f` at `g x`.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_comp
    (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) (hg_nc : ¬EventuallyConst g (𝓝 x)) :
    meromorphicTrailingCoeffAt (f ∘ g) x =
      (meromorphicTrailingCoeffAt (g · - g x) x) ^ (meromorphicOrderAt f (g x)).untop₀ •
      meromorphicTrailingCoeffAt f (g x) := by
  by_cases h : meromorphicOrderAt f ( g x ) = ⊤
  · have : meromorphicTrailingCoeffAt (f ∘ g) x = 0 := by
      apply MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
      rw [meromorphicOrderAt_eq_top_iff] at *
      exact (hg.map_nhdsNE hg_nc) h
    aesop
  · set r := (meromorphicOrderAt f (g x)).untop₀
    obtain ⟨F, h₁F, h₂F, h₃F⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
    have h₁ : meromorphicTrailingCoeffAt (f ∘ g) x
        = meromorphicTrailingCoeffAt ((g · - g x) ^ r • (F ∘ g)) x := by
      apply meromorphicTrailingCoeffAt_congr_nhdsNE
      apply Filter.Tendsto.eventually (hg.map_nhdsNE hg_nc) h₃F
    have h₂ : meromorphicTrailingCoeffAt ((g · - g x) ^ r • (F ∘ g)) x
        = meromorphicTrailingCoeffAt (g · - g x) x ^ r
          • meromorphicTrailingCoeffAt (F ∘ g) x := by
      convert MeromorphicAt.meromorphicTrailingCoeffAt_smul _ _ using 1
      · rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow]
        exact hg.meromorphicAt.sub (by fun_prop)
      · apply_rules [MeromorphicAt.zpow, hg.meromorphicAt.sub, analyticAt_const.meromorphicAt]
      · exact (h₁F.comp hg).meromorphicAt
    rw [h₁, h₂, (h₁F.comp hg).meromorphicTrailingCoeffAt_of_ne_zero h₂F,
      h₁F.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂F h₃F]
    simp_all

@[simp] theorem meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicTrailingCoeffAt (f ∘ fun z ↦ (z + c)) (x - c) = meromorphicTrailingCoeffAt f x := by
  sorry


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
    sorry
  · sorry
  · sorry
  · sorry
