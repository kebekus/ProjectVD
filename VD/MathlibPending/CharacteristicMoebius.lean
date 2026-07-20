/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import VD.MathlibPending.Scaling

/-!
# Invariance of the Characteristic Function under Automorphisms of the Projective Line

As a corollary to the First Main Theorem of Value Distribution Theory, we show that postcomposing a
meromorphic function `f : ℂ → ℂ` with an automorphism of the projective line `ℙ¹(ℂ) = ℂ ∪ {∞}`
changes the characteristic function `characteristic f ⊤` only by a bounded function.

An automorphism of `ℙ¹(ℂ)` is a Möbius transformation `w ↦ (a * w + b) / (c * w + d)` with
discriminant `a * d - b * c ≠ 0`.  The characteristic function plays the role of a height, and the
statement below is the analogue of the fact that heights are invariant under the action of `PGL₂` up
to bounded terms.

The proof decomposes a general Möbius transformation into the standard generators (translations,
inversion, and scaling) and applies the two parts of the First Main Theorem
(`isBigO_characteristic_sub_characteristic_inv` and
`isBigO_characteristic_sub_characteristic_shift`) together with the scaling lemma
`isBigO_characteristic_sub_characteristic_const_mul` established here.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.
-/

open Asymptotics Filter Function Metric MeromorphicOn Real Set Topology ValueDistribution

namespace ValueDistribution

variable {f : ℂ → ℂ}

/-!
## Scaling by a Nonzero Constant
-/

/-!
### LogCounting
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The logCounting function at top is invariant under scaling. -/
@[simp] theorem logCounting_const_smul_top [ProperSpace 𝕜] {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    ValueDistribution.logCounting (s • f) ⊤ = ValueDistribution.logCounting f ⊤ := by
  simp_all [logCounting_top]

/-- The logCounting function at top is invariant under scaling. -/
@[simp] theorem logCounting_fun_const_smul_top [ProperSpace 𝕜] {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    ValueDistribution.logCounting (fun x ↦ s • f x) ⊤ = ValueDistribution.logCounting f ⊤ :=
  logCounting_const_smul_top hs

/-!
### Proximity
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If `f` is circle integrable, then so are its scalar multiples. -/
theorem CircleIntegrable.const_smul' {f : ℂ → E} {c s : ℂ} {R : ℝ} (h : CircleIntegrable f c R) :
    CircleIntegrable (s • f) c R := by
  apply h.smul

@[simp]
theorem circleIntegrable_iff_circleIntegrable_const_smul {f : ℂ → E} {c s : ℂ} {R : ℝ} (h : s ≠ 0) :
    CircleIntegrable (s • f) c R ↔ CircleIntegrable f c R := by
  constructor <;> intro hf
  · rw [show f = s⁻¹ • s • f by simp_all]
    exact hf.const_smul' -- should be fun_prop
  · exact hf.const_smul' -- should be fun_prop

/--
The proximity function `f • g` at `⊤` is less than or equal to the sum of the proximity functions of
`f` and `g`, respectively.
-/
theorem proximity_smul_top_le {f₁ : ℂ → ℂ} {f₂ : ℂ → E} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) :
    proximity (f₁ • f₂) ⊤ ≤ proximity f₁ ⊤ + proximity f₂ ⊤ := by
  calc proximity (f₁ • f₂) ⊤
    _ = circleAverage (fun x ↦ log⁺ (‖f₁ x‖ * ‖f₂ x‖)) 0 := by
      simp [proximity, norm_smul]
    _ ≤ circleAverage (fun x ↦ log⁺ ‖f₁ x‖ + log⁺ ‖f₂ x‖) 0 := by
      intro r
      apply circleAverage_mono
      · simp_rw [← norm_smul]
        -- should be fun_prop
        apply MeromorphicOn.circleIntegrable_posLog_norm
        apply Meromorphic.meromorphicOn
        fun_prop
      · -- should be fun_prop
        apply (MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h₁f₁ x)).add
          (MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h₁f₂ x))
      · exact fun _ _ ↦ posLog_mul
    _ = circleAverage (log⁺ ‖f₁ ·‖) 0 + circleAverage (log⁺ ‖f₂ ·‖) 0 := by
      ext r
      apply circleAverage_add
      · -- should be fun_prop
        exact MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h₁f₁ x)
      · -- should be fun_prop
        exact MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h₁f₂ x)
    _ = proximity f₁ ⊤ + proximity f₂ ⊤ := by simp [proximity]

theorem abs_posLog_mul_sub_posLog_le_posLog_add_posLog {x y : ℝ} (hx : x ≠ 0) :
    |log⁺ (x * y) - log⁺ y| ≤ log⁺ x + log⁺ x⁻¹ := by
  rw [abs_le]
  constructor
  · grind [posLog_mul (x := x⁻¹) (y := x * y), posLog_nonneg]
  · grind [posLog_mul, posLog_nonneg]

theorem isBigO_proximity_top_sub_proximity_const_smul_top {f : ℂ → E} {s : ℂ}
    (hf : Meromorphic f) (hs : s ≠ 0) :
    (proximity f ⊤ - proximity (s • f) ⊤) =O[atTop] (1 : ℝ → ℝ) := by
  apply Asymptotics.isBigO_iff.2
  use log⁺ ‖s‖ + log⁺ ‖s⁻¹‖
  apply eventually_atTop.2
  use 0
  intro r hr
  simp only [proximity, ↓reduceDIte, Pi.smul_apply, Pi.sub_apply, norm_eq_abs, norm_inv,
    Pi.one_apply, norm_one, mul_one]
  rw [← circleAverage_sub]
  · trans circleAverage |(log⁺ ‖f ·‖) - (log⁺ ‖s • f ·‖)| 0 r
    · apply abs_circleAverage_le_circleAverage_abs
    · rw [← circleAverage_const (a := log⁺ ‖s‖ + log⁺ ‖s‖⁻¹)]
      apply circleAverage_mono
      · -- should be fun_prop
        apply CircleIntegrable.abs
        apply CircleIntegrable.sub
        · refine circleIntegrable_posLog_norm_of_nonneg ?_ hr
          intro z hz
          exact hf z
        · refine circleIntegrable_posLog_norm_of_nonneg ?_ hr
          intro z hz
          exact MeromorphicAt.fun_const_smul (hf z) s
      · -- should be fun_prop
        exact circleIntegrable_const (log⁺ ‖s‖ + log⁺ ‖s‖⁻¹) 0 r
      · intro x hx
        simp only [Pi.abs_apply, Pi.sub_apply]
        rw [norm_smul, abs_sub_comm]
        apply abs_posLog_mul_sub_posLog_le_posLog_add_posLog
        simp_all
  · -- should be fun_prop
    refine circleIntegrable_posLog_norm_of_nonneg ?_ hr
    intro z hz
    exact hf z
  · -- should be fun_prop
    refine circleIntegrable_posLog_norm_of_nonneg ?_ hr
    intro z hz
    exact MeromorphicAt.fun_const_smul (hf z) s

/--
Multiplying a meromorphic function by a nonzero constant changes the characteristic function (for
the value `⊤`) only by a bounded function.
-/
theorem isBigO_characteristic_sub_characteristic_const_mul {f : ℂ → ℂ} {s : ℂ}
    (hf : Meromorphic f) (hs : s ≠ 0) :
    (characteristic f ⊤ - characteristic (s • f) ⊤) =O[atTop] (1 : ℝ → ℝ) := by
  unfold characteristic
  rw [logCounting_const_smul_top hs]
  ring_nf
  apply isBigO_proximity_top_sub_proximity_const_smul_top hf hs

/-!
## Postcomposition with an Automorphism of the Projective Line
-/

variable
  {X : Type*} [TopologicalSpace X]
  {Y : Type*}

lemma mem_codiscrete_iff_forall_mem_nhdsNE {S : Set X} :
    S ∈ codiscrete X ↔ ∀ x, S ∈ 𝓝[≠] x := by
  simp [codiscrete, mem_codiscreteWithin_iff_forall_mem_nhdsNE]

lemma eventuallyEq_discrete_iff_forall_eventuallyEq_nhdsNe {f₁ f₂ : X → Y} :
    f₁ =ᶠ[codiscrete X] f₂ ↔ ∀ x, f₁ =ᶠ[𝓝[≠] x] f₂ := by
  simp [EventuallyEq, Filter.Eventually, mem_codiscrete_iff_forall_mem_nhdsNE]

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]


/--
If `f` is meromorphic function on `ℝ` or `ℂ`, then there exists a point where a meromorphic function
`f` has finite order iff `f` has finite order at every point.
-/
theorem Meromorphic.exists_meromorphicOrderAt_eq_top_iff_forall {f : 𝕜 → E} (hf : Meromorphic f) :
    (∃ u, meromorphicOrderAt f u = ⊤) ↔ (∀ u, meromorphicOrderAt f u = ⊤) := by
  have := hf.exists_meromorphicOrderAt_ne_top_iff_forall.not.symm
  aesop

theorem Meromorphic.exists_meromorphicOrderAt_eq_top_iff_eventually_zero {f : 𝕜 → E}
    (hf : Meromorphic f) :
    (∃ u, meromorphicOrderAt f u = ⊤) ↔ (f =ᶠ[codiscrete 𝕜] 0) := by
  rw [hf.exists_meromorphicOrderAt_eq_top_iff_forall]
  constructor <;> intro h
  · apply eventuallyEq_discrete_iff_forall_eventuallyEq_nhdsNe.2
      (fun x ↦meromorphicOrderAt_eq_top_iff.1 (h x))
  · intro _
    rw [meromorphicOrderAt_eq_top_iff, Filter.Eventually]
    apply mem_codiscrete_iff_forall_mem_nhdsNE.1 h

@[simp] lemma proximity_const' {c : E} :
    proximity (fun _ ↦ c) ⊤ = fun _ ↦ log⁺ ‖c‖ := by
  ext r
  simp [proximity, circleAverage_const]

@[simp] theorem characteristic_const {c : ℂ} :
    characteristic (fun _ ↦ c) ⊤ = fun _ ↦ log⁺ ‖c‖ := by
  unfold characteristic
  simp

@[simp] theorem characteristic_zero :
    characteristic (0 : ℂ → ℂ) ⊤ = fun _ ↦ 0 := by
  convert characteristic_const (c := 0)
  · simp
  · simp

/- Private transitivity lemma, used in the proof of
`isBigO_characteristic_sub_characteristic_moebius`. -/
private lemma transitivity₁ {f₁ f₃ : ℝ → ℝ} (f₂ : ℂ → ℂ)
    (h₂₃ : (characteristic f₂ ⊤ - f₃) =O[atTop] (1 : ℝ → ℝ))
    (h₁₂ : (f₁ - characteristic f₂ ⊤) =O[atTop] (1 : ℝ → ℝ)) :
    (f₁ - f₃) =O[atTop] (1 : ℝ → ℝ) := by
  convert h₁₂.add h₂₃
  · exact (congrArg Norm.mk ∘ fun a ↦ a) rfl
  · simp

/- Private transitivity lemma, used in the proof of
`isBigO_characteristic_sub_characteristic_moebius`. -/
private lemma transitivity₂ {f₁ f₂ f₃ : ℂ → ℂ} (h₂₃ : f₂ =ᶠ[codiscrete ℂ] f₃)
    (h₁₂ : (characteristic f₁ ⊤ - characteristic f₂ ⊤) =O[atTop] (1 : ℝ → ℝ)) :
    (characteristic f₁ ⊤ - characteristic f₃ ⊤) =O[atTop] (1 : ℝ → ℝ) := by
  simp_rw [isBigO_iff, eventually_atTop] at *
  obtain ⟨c, a, hc⟩ := h₁₂
  use c, max a 1
  intro r hr
  simp only [Pi.sub_apply, Pi.one_apply, norm_one, mul_one] at *
  rw [characteristic_congr_codiscrete h₂₃.symm (by grind)]
  apply hc r (by aesop)


/--
**Corollary to the First Main Theorem.** Postcomposing a meromorphic function `f : ℂ → ℂ` with an
automorphism `w ↦ (a * w + b) / (c * w + d)` (with `a * d - b * c ≠ 0`) of the projective line
changes the characteristic function for the value `⊤` only by a bounded function.

No nondegeneracy hypothesis on `f` is needed: in the degenerate case where the denominator
`c * f + d` vanishes identically (away from a discrete set), both `f` and the composite are
eventually constant along the codiscrete filter, so both characteristic functions are bounded.
-/
theorem isBigO_characteristic_sub_characteristic_moebius {a b c d : ℂ}
    (hf : Meromorphic f) (hΔ : a * d - b * c ≠ 0) :
    (characteristic f ⊤ - characteristic ((a • f · + b) / (c • f · + d)) ⊤)
      =O[atTop] (1 : ℝ → ℝ) := by
  by_cases hc : c = 0
  · -- Affine case `c = 0`: the map is `w ↦ (a / d) * w + b / d`.
    subst hc
    ring_nf at *
    apply transitivity₁ (a * f · + b)
    · convert isBigO_characteristic_sub_characteristic_const_mul (s := d⁻¹) (f := (a * f · + b))
        (by fun_prop) (by aesop)
      ext x
      simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
      field
    apply transitivity₁ (a * f ·)
    · convert isBigO_characteristic_sub_characteristic_shift (a₀ := -b) (f := a • f)
        (by fun_prop)
      · rfl
      simp
    apply transitivity₁ f
    · convert isBigO_characteristic_sub_characteristic_const_mul (s := a) (f := f)
        (by fun_prop) (by aesop)
      simp
    simp [IsBigO.of_norm_le]
  · -- Case `c ≠ 0`.
    by_cases hord : ∀ z, meromorphicOrderAt (c * f · + d) z ≠ ⊤
    · have hne : ∀ᶠ z in codiscrete ℂ, c * f z + d ≠ 0 := by
        -- Wrong name!
        apply MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero _ (fun u _ ↦ hord u)
        -- should be fun_prop
        apply Meromorphic.meromorphicOn
        fun_prop
      apply transitivity₂ (f₂ := (fun z ↦ a / c + (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹))
      · filter_upwards [hne] with z hz
        rw [Pi.div_apply]
        field_simp [hc, hz, show f z * c + d ≠ 0 by grind, show f z + d / c ≠ 0 by grind]
        ring
      apply transitivity₁ (fun z ↦ (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹)
      · simp_rw [add_comm (a := a / c), ← sub_neg_eq_add (b := a / c)]
        apply isBigO_characteristic_sub_characteristic_shift (by fun_prop)
      apply transitivity₁ (f · + d / c)⁻¹
      · apply isBigO_characteristic_sub_characteristic_const_mul (by fun_prop)
        grind
      apply transitivity₁ (f · + d / c) (isBigO_characteristic_sub_characteristic_inv (by fun_prop))
      apply transitivity₁
      · simp_rw [← sub_neg_eq_add]
        apply isBigO_characteristic_sub_characteristic_shift (by fun_prop)
      rw [sub_self]
      apply Asymptotics.isBigO_const_one
    · -- Degenerate case: the denominator vanishes away from a codiscrete set.
      simp only [ne_eq, not_forall, Decidable.not_not] at hord
      rw [Meromorphic.exists_meromorphicOrderAt_eq_top_iff_eventually_zero (by fun_prop)] at hord
      apply transitivity₁ fun _ ↦ -(d / c)
      · apply transitivity₂ (f₂ := 0)
        · filter_upwards [hord] with z hz
          simp_all
        · -- should be simp
          apply Asymptotics.IsBigO.sub
          · simp only [characteristic_const, norm_neg, Complex.norm_div]
            apply Asymptotics.isBigO_const_one
          · simp only [characteristic_zero]
            apply Asymptotics.isBigO_const_one
      · apply transitivity₂ (f₂ := f) (f₃ := fun _ ↦ -(d / c))
        · filter_upwards [hord] with z hz
          rw [Pi.zero_apply] at hz
          field_simp
          linear_combination hz
        · rw [sub_self]
          apply Asymptotics.isBigO_const_one

end ValueDistribution
