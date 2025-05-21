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

- Formalize the first part of the First Main Theorem, which is the more
  substantial part of the statement.
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
Analogue of `IntervalIntegrable.abs`: If a function real-valued funcion `f` is
circle integrable, then so is `|f|`.
-/
theorem CircleIntegrable.abs {f : ℂ → ℝ} (hf : CircleIntegrable f c R) :
    CircleIntegrable |f| c R := IntervalIntegrable.abs hf

/--
The circle average of a constant function equals the constant.
-/
theorem circleAverage_const (a : ℝ) (c : ℂ) (R : ℝ) : circleAverage (fun _ ↦ a) c R = a := by
  simp only [circleAverage, mul_inv_rev, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring_nf
  simp [mul_inv_cancel₀ pi_ne_zero]

/--
If `f x` equals `a` on for every point of the circle, then the circle average of
`f` equals `a`.
-/
theorem circleAverage_const_on_circle {a : ℝ} (hf : ∀ x ∈ Metric.sphere c |R|, f x = a) :
    circleAverage f c R = a := by
  rw [circleAverage]
  conv =>
    left; arg 2; arg 1
    intro θ
    rw [hf (circleMap c R θ) (circleMap_mem_sphere' c R θ)]
  apply circleAverage_const a c R

/--
If `f x` is smaller than `a` on for every point of the circle, then the circle
average of `f` is smaller than `a`.
-/
theorem circleAverage_mono_on_of_le_circle {a : ℝ} (hf : CircleIntegrable f c R)
    (h₂f : ∀ x ∈ Metric.sphere c |R|, f x ≤ a) :
    circleAverage f c R ≤ a := by
  rw [← circleAverage_const a c |R|, circleAverage, circleAverage, smul_eq_mul, smul_eq_mul,
    mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
  apply intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos) hf
  apply intervalIntegral.intervalIntegrable_const a
  exact fun θ _ ↦ h₂f (circleMap c R θ) (circleMap_mem_sphere' c R θ)

/--
Analogue of `intervalIntegral.abs_integral_le_integral_abs`: The absolute value
of a circle average is less than or equal to the circle average of the absolute
value of the function.
-/
theorem abs_circleAverage_le_circleAverage_abs :
    |circleAverage f c R| ≤ circleAverage |f| c R := by
  rw [circleAverage, circleAverage, smul_eq_mul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 two_pi_pos),
    mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
  exact intervalIntegral.abs_integral_le_integral_abs (le_of_lt two_pi_pos)

/--
Variant of `posLog_add` for norms of elements in normed additive commutative
groups, using monotonicity of `log⁺` and the triangle inequality.
-/
lemma posLog_norm_add_le {E : Type*} [NormedAddCommGroup E] (a b : E) :
    log⁺ ‖a + b‖ ≤ log⁺ ‖a‖ + log⁺ ‖b‖ + log 2 := by
  calc log⁺ ‖a + b‖
  _ ≤ log⁺ (‖a‖ + ‖b‖) := by
    apply monotoneOn_posLog _ _ (norm_add_le a b)
    <;> simp [add_nonneg (norm_nonneg a) (norm_nonneg b)]
  _ ≤ log⁺ ‖a‖ + log⁺ ‖b‖ + log 2 := by
    convert posLog_add using 1
    ring

/-!
# File Body
-/

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {a₀ : E}

open Asymptotics Filter Real

/-!
## Second part of the First Main Theorem
-/

/--
Second part of the First Main Theorem of Value Distribution Theory, quantitative
version: If `f` is meromorphic on the complex plane, then the characteristic
functions (for value `⊤`) of `f` and `f - a₀` differ at most by `log⁺ ‖a₀‖ + log
2`.
-/
theorem FirstMainTheorem₂_quant {r : ℝ} (h : MeromorphicOn f ⊤) :
    |characteristic f ⊤ r - characteristic (f · - a₀) ⊤ r| ≤ log⁺ ‖a₀‖ + log 2 := by
  have h₁f : CircleIntegrable (fun x ↦ log⁺ ‖f x‖) 0 r :=
    MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h x trivial)
  have h₂f : CircleIntegrable (fun x ↦ log⁺ ‖f x - a₀‖) 0 r := by
    apply MeromorphicOn.circleIntegrable_posLog_norm
    apply MeromorphicOn.sub (fun x a => h x trivial) (MeromorphicOn.const a₀)
  rw [← Pi.sub_apply, characteristic_sub_characteristic_eq_proximity_sub_proximity h]
  simp only [proximity, reduceDIte, Pi.sub_apply, ← circleAverage_sub h₁f h₂f]
  apply le_trans abs_circleAverage_le_circleAverage_abs
  apply circleAverage_mono_on_of_le_circle
  apply (h₁f.sub h₂f).abs
  intro θ hθ
  simp only [Pi.abs_apply, Pi.sub_apply]
  by_cases h : 0 ≤ log⁺ ‖f θ‖ - log⁺ ‖f θ - a₀‖
  · simpa [abs_of_nonneg h, sub_le_iff_le_add, add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
      using (posLog_norm_add_le (f θ - a₀) a₀)
  · simp [abs_of_nonpos (le_of_not_ge h), neg_sub, sub_le_iff_le_add, add_comm (log⁺ ‖a₀‖ + log 2),
      ← add_assoc]
    convert posLog_norm_add_le (-f θ) (a₀) using 2
    · rw [← norm_neg]
      abel_nf
    · simp

/--
Second part of the First Main Theorem of Value Distribution Theory, qualitative
version: If `f` is meromorphic on the complex plane, then the characteristic
functions for the value `⊤` of the function `f` and `f - a₀` agree
asymptotically up to a bounded function.
-/
theorem FirstMainTheorem₂_qual (h : MeromorphicOn f ⊤) :
    |(characteristic f ⊤) - (characteristic (f · - a₀) ⊤)| =O[atTop] (1 : ℝ → ℝ) := by
  simp_rw [isBigO_iff', eventually_atTop]
  use log⁺ ‖a₀‖ + log 2, add_pos_of_nonneg_of_pos posLog_nonneg (log_pos one_lt_two), 0
  simp [FirstMainTheorem₂_quant h]

end ValueDistribution
