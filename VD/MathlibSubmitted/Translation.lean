/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.PoissonJensen0

/-!
# Translation Invariance of Meromorphic Notions

This file collects lemmas showing that `MeromorphicAt`, `MeromorphicOn`,
`Meromorphic`, `meromorphicOrderAt`, `meromorphicTrailingCoeffAt`, and `divisor`
are invariant under translation, including specializations to balls, closed
balls, and spheres.

Partially by Aristotle AI
-/

open Complex Filter Function MeromorphicOn Metric Real Set Topology --ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {x : 𝕜}

/-- `MeromorphicAt` is invariant under translation. -/
@[simp] theorem meromorphicAt_comp_add_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (f ∘ (· + c)) (x - c) ↔ MeromorphicAt f x := by
  constructor
  · intro h
    convert h.comp_analyticAt (g := fun z ↦ z - c) (by fun_prop)
    aesop
  · intro h
    rw [(by ring : x = (x - c) + c)] at h
    exact h.comp_analyticAt (g := fun z ↦ z + c) (by fun_prop)

/-- `MeromorphicAt` is invariant under translation. -/
@[simp] theorem meromorphicAt_fun_comp_add_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (fun z ↦ f (z + c)) (x - c) ↔ MeromorphicAt f x :=
  meromorphicAt_comp_add_const_iff_meromorphicAt

/-- `MeromorphicAt` is invariant under translation. -/
@[simp] theorem meromorphicAt_comp_sub_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (f ∘ (· - c)) (x + c) ↔ MeromorphicAt f x := by
  simp [← meromorphicAt_fun_comp_add_const_iff_meromorphicAt (f := f) (c := -c), ← sub_eq_add_neg]
  rfl

/-- `MeromorphicAt` is invariant under translation. -/
@[simp] theorem meromorphicAt_fun_comp_sub_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (fun z ↦ f (z - c)) (x + c) ↔ MeromorphicAt f x :=
  meromorphicAt_comp_sub_const_iff_meromorphicAt

/-- `MeromorphicOn` is invariant under translation. -/
@[simp] theorem meromorphicOn_comp_add_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} {f : 𝕜 → E} :
    MeromorphicOn (f ∘ (· + c)) {x | x + c ∈ U} ↔ MeromorphicOn f U := by
  constructor
  · intro h y hy
    rw [← meromorphicAt_fun_comp_add_const_iff_meromorphicAt (c := c)]
    apply h
    aesop
  · intro h y hy
    rw [← meromorphicAt_comp_sub_const_iff_meromorphicAt (c := c),
      (by aesop : ((f ∘ fun z ↦ z + c) ∘ fun z ↦ z - c) = f)]
    exact h (y + c) (mem_preimage.mp hy)

/-- `MeromorphicOn` is invariant under translation. -/
@[simp] theorem meromorphicOn_fun_comp_add_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} {f : 𝕜 → E} :
    MeromorphicOn (fun z ↦ f (z + c)) {x | x + c ∈ U} ↔ MeromorphicOn f U :=
  meromorphicOn_comp_add_const_iff_meromorphicOn

/-- `MeromorphicOn` is invariant under translation. -/
@[simp] theorem meromorphicOn_comp_sub_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} {f : 𝕜 → E} :
    MeromorphicOn (f ∘ (· - c)) {x | x - c ∈ U} ↔ MeromorphicOn f U := by
  simp [← meromorphicOn_comp_add_const_iff_meromorphicOn (f := f) (c := -c), ← sub_eq_add_neg]

/-- `MeromorphicOn` is invariant under translation. -/
@[simp] theorem meromorphicOn_fun_comp_sub_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} {f : 𝕜 → E} :
    MeromorphicOn (fun z ↦ f (z - c)) {x | x - c ∈ U} ↔ MeromorphicOn f U :=
  meromorphicOn_comp_sub_const_iff_meromorphicOn

/-- A translated ball is a ball. -/
theorem ball_eq_setOf_sub_mem_ball {c : E} {R : ℝ} :
    {x | x - c ∈ ball 0 R} = Metric.ball c R := by
  ext x
  rw [mem_ball_iff_norm]
  simp

/-- A translated closed ball is a closed ball. -/
theorem closedBall_eq_setOf_sub_mem_closedBall {c : E} {R : ℝ} :
    {x | x - c ∈ closedBall 0 R} = Metric.closedBall c R := by
  ext x
  rw [mem_closedBall_iff_norm]
  simp

/-- A translated sphere is a sphere. -/
theorem sphere_eq_setOf_sub_mem_sphere {c : E} {R : ℝ} :
    {x | x - c ∈ sphere 0 R} = Metric.sphere c R := by
  ext x
  rw [mem_sphere_iff_norm]
  simp

/--
`MeromorphicOn` is invariant under translation, special case where the set is a
ball.
-/
@[simp] theorem meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball
    {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    MeromorphicOn (f ∘ (· - c)) (Metric.ball c R) ↔ MeromorphicOn f (Metric.ball 0 R) := by
  convert meromorphicOn_comp_sub_const_iff_meromorphicOn
  rw [ball_eq_setOf_sub_mem_ball]

/--
`MeromorphicOn` is invariant under translation, special case where the set is a
ball.
-/
@[simp] theorem meromorphicOn_ball_fun_comp_sub_const_iff_meromorphicOn_ball
    {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    MeromorphicOn (fun z ↦ f (z - c)) (Metric.ball c R) ↔ MeromorphicOn f (Metric.ball 0 R) :=
  meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball

/--
`MeromorphicOn` is invariant under translation, special case where the set is a
closed ball.
-/
@[simp] theorem meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall
    {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    MeromorphicOn (f ∘ (· - c)) (Metric.closedBall c R)
      ↔ MeromorphicOn f (Metric.closedBall 0 R) := by
  convert meromorphicOn_comp_sub_const_iff_meromorphicOn
  rw [closedBall_eq_setOf_sub_mem_closedBall]

/--
`MeromorphicOn` is invariant under translation, special case where the set is a
closed ball.
-/
@[simp] theorem meromorphicOn_closedBall_fun_comp_sub_const_iff_meromorphicOn_closedBall
    {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    MeromorphicOn (fun z ↦ f (z - c)) (Metric.closedBall c R)
      ↔ MeromorphicOn f (Metric.closedBall 0 R) :=
  meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall

/--
`MeromorphicOn` is invariant under translation, special case where the set is a
sphere.
-/
@[simp] theorem meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere
    {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    MeromorphicOn (f ∘ (· - c)) (Metric.sphere c R) ↔ MeromorphicOn f (Metric.sphere 0 R) := by
  convert meromorphicOn_comp_sub_const_iff_meromorphicOn
  rw [sphere_eq_setOf_sub_mem_sphere]

/--
`MeromorphicOn` is invariant under translation, special case where the set is a
sphere.
-/
@[simp] theorem meromorphicOn_sphere_fun_comp_sub_const_iff_meromorphicOn_sphere
    {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    MeromorphicOn (fun z ↦ f (z - c)) (Metric.sphere c R) ↔ MeromorphicOn f (Metric.sphere 0 R) :=
  meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere

/-- `Meromorphic` is invariant under translation. -/
@[simp] theorem meromorphic_comp_add_const_iff_meromorphic {c : 𝕜} {f : 𝕜 → E} :
    Meromorphic (f ∘ (· + c)) ↔ Meromorphic f := by
  constructor
  · intro h x
    rw [← meromorphicAt_comp_add_const_iff_meromorphicAt (c := c)]
    exact h (x - c)
  · intro h x
    rw [← meromorphicAt_comp_sub_const_iff_meromorphicAt (c := c)]
    convert h (x + c)
    aesop

/-- `Meromorphic` is invariant under translation. -/
@[simp] theorem meromorphic_fun_comp_add_const_iff_meromorphic {c : 𝕜} {f : 𝕜 → E} :
    Meromorphic (fun z ↦ f (z + c)) ↔ Meromorphic f :=
  meromorphic_comp_add_const_iff_meromorphic

/-- `Meromorphic` is invariant under translation. -/
@[simp] theorem meromorphic_comp_sub_const_iff_meromorphic {c : 𝕜} {f : 𝕜 → E} :
    Meromorphic (f ∘ (· - c)) ↔ Meromorphic f := by
  nth_rw 2 [← meromorphic_comp_add_const_iff_meromorphic (c := -c)]
  simp_rw [sub_eq_add_neg]

/-- `Meromorphic` is invariant under translation. -/
@[simp] theorem meromorphic_fun_comp_sub_const_iff_meromorphic {c : 𝕜} {f : 𝕜 → E} :
    Meromorphic (fun z ↦ f (z - c)) ↔ Meromorphic f :=
  meromorphic_comp_sub_const_iff_meromorphic

open scoped Classical in
/--
The analytic order of the function `(· - c)` at `x` is one if `x = c` and zero
otherwise.
-/
@[simp] theorem analyticOrderAt_id_sub_const {c x : 𝕜} :
    analyticOrderAt (· - c) x = if x = c then 1 else 0 := by
  by_cases h : x = c
  · have := analyticOrderAt_centeredMonomial (n := 1) (z₀ := x)
    simp_all [pow_one]
  · simp only [h, reduceIte]
    apply analyticOrderAt_eq_zero.2
    grind

/-- `meromorphicOrderAt` is invariant under translation. -/
@[simp] theorem meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicOrderAt (f ∘ (· + c)) (x - c) = meromorphicOrderAt f x := by
  by_cases h : ¬ MeromorphicAt f x
  · simp_all
  rw [MeromorphicAt.meromorphicOrderAt_comp (by simp_all) (by fun_prop)]
  · have {a b c : 𝕜} : a + b - c = a - (c - b) := by ring
    simp [this]
  · have {a b c : 𝕜} : a + b - (c - b + b) = a - (c - b) := by ring
    simp_rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, this]
    simp

/-- `meromorphicOrderAt` is invariant under translation. -/
@[simp] theorem meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicOrderAt (fun z ↦ f (z + c)) (x - c) = meromorphicOrderAt f x :=
  meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt

/-- `meromorphicOrderAt` is invariant under translation. -/
@[simp] theorem meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicOrderAt (f ∘ (· - c)) (x + c) = meromorphicOrderAt f x := by
  simp [← meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (f := f) (c := -c),
    ← sub_eq_add_neg]

/-- `meromorphicOrderAt` is invariant under translation. -/
@[simp] theorem meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicOrderAt (fun z ↦ f (z - c)) (x + c) = meromorphicOrderAt f x :=
  meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → 𝕜} {x : 𝕜}

/--
If `g` is analytic at `x` and not locally constant, and `f` is meromorphic at `g
x`, express the trailing coefficient of `f ∘ g` at `x` in terms of `g` and `f`.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_comp (hf : MeromorphicAt f (g x))
    (hg : AnalyticAt 𝕜 g x) (hg_nc : ¬EventuallyConst g (𝓝 x)) :
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
    rw [h₁, MeromorphicAt.meromorphicTrailingCoeffAt_smul (by fun_prop) (by fun_prop),
      (h₁F.comp hg).meromorphicTrailingCoeffAt_of_ne_zero h₂F,
      h₁F.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂F h₃F]
    simp_all only [ne_eq, comp_apply, not_false_eq_true, smul_left_inj]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)

open scoped Classical in
/-- `meromorphicTrailingCoefficientAt` is invariant under translation. -/
@[simp] theorem meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt
    {c : 𝕜} {f : 𝕜 → E} :
    meromorphicTrailingCoeffAt (f ∘ (· + c)) (x - c) = meromorphicTrailingCoeffAt f x := by
  by_cases h : ¬ MeromorphicAt f x
  · simp_all
  rw [not_not] at h
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_comp (by rwa [sub_add_cancel]) (by fun_prop),
    sub_add_cancel]
  · have {a b c : 𝕜} : a + b - c = a - (c - b) := by ring
    simp [this, meromorphicTrailingCoeffAt_id_sub_const] -- simp only should be enough!
  · rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top]
    have {a b c : 𝕜} : a + c - (b - c + c) = a - (b - c) := by ring
    simp_rw [this]
    simp

/-- `meromorphicTrailingCoefficientAt` is invariant under translation. -/
@[simp] theorem meromorphicTrailingCoeffAt_fun_comp_add_const_eq_meromorphicTrailingCoeffAt
    {c : 𝕜} {f : 𝕜 → E} :
    meromorphicTrailingCoeffAt (fun z ↦ f (z + c)) (x - c) = meromorphicTrailingCoeffAt f x :=
  meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt

/--
The divisor of a function `f` evaluates to zero if `f` is not meromorphic.
-/
@[simp] theorem divisor_eq_zero_of_not_meromorphicOn {U : Set 𝕜} {w : 𝕜}
    (hf : ¬ MeromorphicOn f U) :
    divisor f U w = 0 := by
  unfold divisor
  aesop

/-- Divisors are invariant under translation. -/
@[simp] theorem divisor_comp_add_const_eq_divisor {c x : 𝕜} {U : Set 𝕜} {f : 𝕜 → E} :
    divisor (f ∘ (· + c)) {x | x + c ∈ U} (x - c) = divisor f U x := by
  by_cases h : ¬ MeromorphicOn f U
  · have := (meromorphicOn_comp_add_const_iff_meromorphicOn (c := c) (U := U) (f := f)).not.2 h
    simp_all
  rw [not_not] at h
  have := (meromorphicOn_comp_add_const_iff_meromorphicOn (c := c) (U := U) (f := f)).2 h
  by_cases h₁ : ¬ x ∈ U
  · rw [locallyFinsuppWithin.apply_eq_zero_of_notMem, locallyFinsuppWithin.apply_eq_zero_of_notMem]
    <;> aesop
  rw [divisor_apply, divisor_apply]
  <;> aesop

/-- Divisors are invariant under translation. -/
@[simp] theorem divisor_fun_comp_add_const_eq_divisor {c x : 𝕜} {U : Set 𝕜} {f : 𝕜 → E} :
    divisor (fun z ↦ f (z + c)) {x | x + c ∈ U} (x - c) = divisor f U x :=
  divisor_comp_add_const_eq_divisor

/-- Divisors are invariant under translation. -/
@[simp] theorem divisor_comp_sub_const_eq_divisor {c x : 𝕜} {U : Set 𝕜} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) {x | x - c ∈ U} (x + c) = divisor f U x := by
  nth_rw 2 [← divisor_comp_add_const_eq_divisor (c := -c)]
  congr 2
  <;> simp [sub_eq_add_neg]

/-- Divisors are invariant under translation, special case where the set is a ball.. -/
@[simp] theorem divisor_ball_comp_add_const_eq_divisor_ball {c x : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) (Metric.ball c R) (x + c) = divisor f (Metric.ball 0 R) x := by
  nth_rw 2 [← divisor_comp_sub_const_eq_divisor (c := c)]
  congr
  all_goals
    rw [ball_eq_setOf_sub_mem_ball]

/-- Divisors are invariant under translation, special case where the set is a ball. -/
@[simp] theorem divisor_ball_fun_comp_add_const_eq_divisor_ball {c x : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (fun z ↦ f (z - c)) (Metric.ball c R) (x + c) = divisor f (Metric.ball 0 R) x :=
  divisor_ball_comp_add_const_eq_divisor_ball

/-- Divisors are invariant under translation, special case where the set is a closed ball. -/
@[simp] theorem divisor_closedBall_comp_add_const_eq_divisor_closedBall
    {c x : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) (Metric.closedBall c R) (x + c)
      = divisor f (Metric.closedBall 0 R) x := by
  nth_rw 2 [← divisor_comp_sub_const_eq_divisor (c := c)]
  congr
  all_goals
    rw [closedBall_eq_setOf_sub_mem_closedBall]

/-- Divisors are invariant under translation, special case where the set is a closed ball. -/
@[simp] theorem divisor_closedBall_fun_comp_add_const_eq_divisor_closedBall
    {c x : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (fun z ↦ f (z - c)) (Metric.closedBall c R) (x + c)
      = divisor f (Metric.closedBall 0 R) x :=
  divisor_closedBall_comp_add_const_eq_divisor_closedBall

/-- Divisors are invariant under translation, special case where the set is a sphere. -/
@[simp] theorem divisor_sphere_comp_add_const_eq_divisor_sphere {c x : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) (Metric.sphere c R) (x + c) = divisor f (Metric.sphere 0 R) x := by
  nth_rw 2 [← divisor_comp_sub_const_eq_divisor (c := c)]
  congr
  all_goals
    rw [sphere_eq_setOf_sub_mem_sphere]

/-- Divisors are invariant under translation, special case where the set is a sphere. -/
@[simp] theorem divisor_sphere_fun_comp_add_const_eq_divisor_sphere {c x : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (fun z ↦ f (z - c)) (Metric.sphere c R) (x + c) = divisor f (Metric.sphere 0 R) x :=
  divisor_sphere_comp_add_const_eq_divisor_sphere
