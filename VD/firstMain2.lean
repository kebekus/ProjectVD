/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.ProximityFunction
import VD.ToMathlib.CharacteristicFunction

/-!
# The First Main Theorem of Value Distribution Theory

The First Main Theorem of Value Distribution Theory is a two-part statement,
establishing invariance of the characteristic function `characteristic f ⊤`
under modifications of `f`.

- If `f` is meromorphic on the complex plane, then the characteristic functions
  for the value `⊤` of the function `f` and `f⁻¹` agree up to a constant, see
  Proposition 2.1 on p. 168 of [Lang, *Introduction to Complex Hyperbolic
  Spaces*][MR886677].

- If `f` is meromorphic on the complex plane, then the characteristic functions
  for the value `⊤` of the function `f` and `f - const` agree up to a constant,
  see Proposition 2.2 on p. 168 of [Lang, *Introduction to Complex Hyperbolic
  Spaces*][MR886677]

See Section~VI.2 of [Lang, *Introduction to Complex Hyperbolic
Spaces*][MR886677] or Section~1.1 of [Noguchi-Winkelmann, *Nevanlinna Theory in
Several Complex Variables and Diophantine Approximation*][MR3156076] for a
detailed discussion.

### TODO

- Formalize the first part of the First Main Theorem.
-/



/-!
# Circle Averages
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
  {f f₁ f₂ : ℂ → ℝ} {c : ℂ} {R : ℝ} {a : 𝕜}

open Real

/--
If `f x` is smaller than `a` on for every point of the circle, then the circle
average of `f` is smaller than `a`.
-/
theorem circleAverage_const {a : ℝ} :
    circleAverage (fun _ ↦ a) c R = a := by
  simp only [circleAverage, mul_inv_rev, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring_nf
  simp [mul_inv_cancel₀ pi_ne_zero]

/--
If `f x` is smaller than `a` on for every point of the circle, then the circle
average of `f` is smaller than `a`.
-/
theorem circleAverage_le_of_le {a : ℝ} (hf : CircleIntegrable f c R)
    (h₂f : ∀ x ∈ Metric.sphere c |R|, f x < a) :
    circleAverage f c R ≤ a := by
  rw [← circleAverage_const (a := a) (c := c) (R := |R|)]
  unfold circleAverage
  rw [smul_eq_mul, smul_eq_mul]
  rw [mul_le_mul_iff_of_pos_left]
  apply intervalIntegral.integral_mono_on_of_le_Ioo

  unfold CircleIntegrable at hf
  have : 0 ≤ 2 * π := by sorry
  have Z := intervalIntegral.integral_mono_on_of_le_Ioo this hf (g := fun z ↦ a)


  sorry



namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {a₀ : E}

open Asymptotics Real

/-!
## Second part of the First Main Theorem
-/

/--
Second part of the First Main Theorem of Value Distribution Theory, quantitative
version: If `f` is meromorphic on the complex plane, then the characteristic
functions (for value `⊤`) of `f` and `f - a₀` differ at most by `log⁺ ‖a₀‖ + log
2`.
-/
theorem FirstMainTheorem₂ {r : ℝ} (h : MeromorphicOn f ⊤) :
    |characteristic f ⊤ r - characteristic (f · - a₀) ⊤ r| ≤ log⁺ ‖a₀‖ + log 2 := by
  rw [← Pi.sub_apply, characteristic_sub_characteristic_eq_proximity_sub_proximity h]
  simp only [proximity, reduceDIte, Pi.sub_apply]
  rw [← circleAverage_sub]
  rw [circleAverage]

  let g := f - (fun _ ↦ a₀)

  have t₀₀ (x : ℝ) : log⁺ ‖f (circleMap 0 r x)‖ ≤ log⁺ ‖g (circleMap 0 r x)‖ + log⁺ ‖a₀‖ + log 2 := by
    unfold g
    simp only [Pi.sub_apply]

    calc log⁺ ‖f (circleMap 0 r x)‖
    _ = log⁺ ‖g (circleMap 0 r x) + a₀‖ := by
      unfold g
      simp
    _ ≤ log⁺ (‖g (circleMap 0 r x)‖ + ‖a₀‖) := by
      apply monotoneOn_posLog
      refine Set.mem_Ici.mpr ?_
      apply norm_nonneg
      refine Set.mem_Ici.mpr ?_
      apply add_nonneg
      apply norm_nonneg
      apply norm_nonneg
      --
      apply norm_add_le
    _ ≤ log⁺ ‖g (circleMap 0 r x)‖ + log⁺ ‖a₀‖ + log 2 := by
      convert posLog_add using 1
      ring

  have t₁₀ (x : ℝ) : log⁺ ‖f (circleMap 0 r x)‖ - log⁺ ‖g (circleMap 0 r x)‖ ≤ log⁺ ‖a₀‖ + log 2 := by
    rw [sub_le_iff_le_add]
    nth_rw 1 [add_comm]
    rw [←add_assoc]
    apply t₀₀ x
  clear t₀₀

  have t₀₁ (x : ℝ) : log⁺ ‖g (circleMap 0 r x)‖ ≤ log⁺ ‖f (circleMap 0 r x)‖ + log⁺ ‖a₀‖ + log 2 := by
    unfold g
    simp only [Pi.sub_apply]

    calc log⁺ ‖g (circleMap 0 r x)‖
    _ = log⁺ ‖f (circleMap 0 r x) - a₀‖ := by
      unfold g
      simp
    _ ≤ log⁺ (‖f (circleMap 0 r x)‖ + ‖a₀‖) := by
      apply monotoneOn_posLog
      refine Set.mem_Ici.mpr ?_
      apply norm_nonneg
      refine Set.mem_Ici.mpr ?_
      apply add_nonneg
      apply norm_nonneg
      apply norm_nonneg
      --
      apply norm_sub_le
    _ ≤ log⁺ ‖f (circleMap 0 r x)‖ + log⁺ ‖a₀‖ + log 2 := by
      convert posLog_add using 1
      ring

  have t₁₁ (x : ℝ) : log⁺ ‖g (circleMap 0 r x)‖ - log⁺ ‖f (circleMap 0 r x)‖ ≤ log⁺ ‖a₀‖ + log 2 := by
    rw [sub_le_iff_le_add]
    nth_rw 1 [add_comm]
    rw [←add_assoc]
    apply t₀₁ x
  clear t₀₁

  have t₂ {x : ℝ} : ‖log⁺ ‖f (circleMap 0 r x)‖ - log⁺ ‖g (circleMap 0 r x)‖‖ ≤ log⁺ ‖a₀‖ + log 2 := by
    by_cases h : 0 ≤ log⁺ ‖f (circleMap 0 r x)‖ - log⁺ ‖g (circleMap 0 r x)‖
    · rw [norm_of_nonneg h]
      exact t₁₀ x
    · rw [norm_of_nonpos (by linarith)]
      rw [neg_sub]
      exact t₁₁ x
  clear t₁₀ t₁₁

  have s₀ : ‖∫ (x : ℝ) in (0)..(2 * π), log⁺ ‖f (circleMap 0 r x)‖ - log⁺ ‖g (circleMap 0 r x)‖‖ ≤ (log⁺ ‖a₀‖ + log 2) * |2 * π - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    exact t₂
  clear t₂
  simp only [norm_eq_abs, sub_zero] at s₀
  rw [smul_eq_mul, abs_mul]

  have s₁ : |(2 * π)⁻¹| * |∫ (x : ℝ) in (0)..(2 * π), log⁺ ‖f (circleMap 0 r x)‖ - log⁺ ‖g (circleMap 0 r x)‖| ≤ |(2 * π)⁻¹| * ((log⁺ ‖a₀‖ + log 2) * |2 * π|) := by
    apply mul_le_mul_of_nonneg_left
    exact s₀
    apply abs_nonneg
  have : |(2 * π)⁻¹| * ((log⁺ ‖a₀‖ + log 2) * |2 * π|) = log⁺ ‖a₀‖ + log 2 := by
    rw [mul_comm, mul_assoc]
    have : |2 * π| * |(2 * π)⁻¹| = 1 := by
      rw [abs_mul, abs_inv, abs_mul]
      rw [abs_of_pos pi_pos]
      simp [pi_ne_zero]
      ring_nf
      simp [pi_ne_zero]
    rw [this]
    simp
  rw [this] at s₁
  assumption
  --
  apply MeromorphicOn.circleIntegrable_posLog_norm
  exact fun x a => h x trivial
  --
  apply MeromorphicOn.circleIntegrable_posLog_norm (f := fun z ↦ f z - a₀)
  apply MeromorphicOn.sub
  exact fun x a => h x trivial
  apply MeromorphicOn.const a₀

/--
Second part of the First Main Theorem of Value Distribution Theory, qualitative
version: If `f` is meromorphic on the complex plane, then the characteristic
functions for the value `⊤` of the function `f` and `f - a₀` agree
asymptotically up to a bounded function.
-/
theorem FirstMainTheorem₂' (h : MeromorphicOn f ⊤) :
    |(characteristic f ⊤) - (characteristic (f · - a₀) ⊤)| =O[Filter.atTop] (1 : ℝ → ℝ) := by
  simp_rw [isBigO_iff', Filter.eventually_atTop]
  use posLog ‖a₀‖ + log 2, add_pos_of_nonneg_of_pos posLog_nonneg (log_pos one_lt_two), 0
  simp [FirstMainTheorem₂ h]

end ValueDistribution
