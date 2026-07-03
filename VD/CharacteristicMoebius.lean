/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import VD.MathlibPending.BoundednessCharacteristic
import VD.MathlibPending.Scaling

/-!
# Invariance of the Characteristic Function under Automorphisms of the Projective Line

As a corollary to the First Main Theorem of Value Distribution Theory, we show that postcomposing a
meromorphic function `f : ℂ → ℂ` with an automorphism of the projective line `ℙ¹(ℂ) = ℂ ∪ {∞}`
changes the characteristic function `characteristic f ⊤` only by a bounded function.

An automorphism of `ℙ¹(ℂ)` is a Möbius transformation `w ↦ (a * w + b) / (c * w + d)` with `a * d -
b * c ≠ 0`.  The characteristic function plays the role of a height, and the statement below is the
analogue of the fact that heights are invariant under the action of `PGL₂` up to bounded terms.

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
  · have : f = s⁻¹ • s • f := by aesop
    rw [this]
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
        apply MeromorphicOn.circleIntegrable_posLog_norm
        apply Meromorphic.meromorphicOn
        fun_prop
      · apply (MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h₁f₁ x)).add
          (MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h₁f₂ x))
      · exact fun _ _ ↦ posLog_mul
    _ = circleAverage (log⁺ ‖f₁ ·‖) 0 + circleAverage (log⁺ ‖f₂ ·‖) 0 := by
      ext r
      apply circleAverage_add
      · exact MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h₁f₁ x)
      · exact MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h₁f₂ x)
    _ = proximity f₁ ⊤ + proximity f₂ ⊤ := by simp [proximity]

theorem abs_posLog_mul_sub_posLog_le_posLog_add_posLog {x y : ℝ} (hx : x ≠ 0) :
    |log⁺ (x * y) - log⁺ y| ≤ log⁺ x + log⁺ x⁻¹ := by
  rw [abs_le]
  constructor
  · grind [(posLog_mul (x := x⁻¹) (y := x * y)), posLog_nonneg]
  · grind [posLog_mul, posLog_nonneg]

theorem isBigO_proximity_top_sub_proximity_const_smul_top {f : ℂ → E} {s : ℂ}
    (hf : Meromorphic f) (hs : s ≠ 0) :
    (proximity (s • f) ⊤ - proximity f ⊤) =O[atTop] (1 : ℝ → ℝ) := by
  apply Asymptotics.isBigO_iff.2
  use log⁺ ‖s‖ + log⁺ ‖s⁻¹‖
  apply eventually_atTop.2
  use 0
  intro r hr
  simp only [proximity, ↓reduceDIte, Pi.smul_apply, Pi.sub_apply, norm_eq_abs, norm_inv,
    Pi.one_apply, norm_one, mul_one]
  rw [← circleAverage_sub]
  · trans circleAverage |(log⁺ ‖s • f ·‖) - (log⁺ ‖f ·‖)| 0 r
    · apply abs_circleAverage_le_circleAverage_abs
    · rw [← circleAverage_const (a := log⁺ ‖s‖ + log⁺ ‖s‖⁻¹)]
      apply circleAverage_mono
      · -- should be fun_prop
        apply CircleIntegrable.abs
        apply CircleIntegrable.sub
        · refine circleIntegrable_posLog_norm_of_nonneg ?_ hr
          intro z hz
          exact MeromorphicAt.fun_const_smul (hf z) s
        · refine circleIntegrable_posLog_norm_of_nonneg ?_ hr
          intro z hz
          exact hf z
      · -- should be fun_prop
        exact circleIntegrable_const (log⁺ ‖s‖ + log⁺ ‖s‖⁻¹) 0 r
      · intro x hx
        simp only [Pi.abs_apply, Pi.sub_apply]
        rw [norm_smul]
        apply abs_posLog_mul_sub_posLog_le_posLog_add_posLog
        simp_all
  · -- should be fun_prop
    refine circleIntegrable_posLog_norm_of_nonneg ?_ hr
    intro z hz
    exact MeromorphicAt.fun_const_smul (hf z) s
  · -- should be fun_prop
    refine circleIntegrable_posLog_norm_of_nonneg ?_ hr
    intro z hz
    exact hf z

/--
Multiplying a meromorphic function by a nonzero constant changes the characteristic function (for
the value `⊤`) only by a bounded function.
-/
theorem isBigO_characteristic_sub_characteristic_const_mul {f : ℂ → ℂ} {s : ℂ}
    (hf : Meromorphic f) (hs : s ≠ 0) :
    (characteristic (s • f) ⊤ - characteristic f ⊤) =O[atTop] (1 : ℝ → ℝ) := by
  unfold characteristic
  rw [logCounting_const_smul_top hs]
  ring_nf
  apply isBigO_proximity_top_sub_proximity_const_smul_top hf hs

/-!
## Postcomposition with an Automorphism of the Projective Line
-/

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
    (characteristic ((a • f · + b) / (c • f · + d)) ⊤ - characteristic f ⊤)
      =O[atTop] (1 : ℝ → ℝ) := by
  -- A helper to reverse the order of a bounded difference.
  have flip : ∀ {A B : ℝ → ℝ}, (A - B) =O[atTop] (1 : ℝ → ℝ) → (B - A) =O[atTop] (1 : ℝ → ℝ) := by
    intro A B h
    rw [← isBigO_neg_left]
    aesop
  by_cases hc : c = 0
  · -- Affine case `c = 0`: the map is `w ↦ (a / d) * w + b / d`.
    subst hc
    simp_all only [mul_zero, sub_zero, ne_eq, mul_eq_zero, not_or, smul_eq_mul, zero_mul, zero_add]
    have : ((a * f · + b) / (fun _ ↦ d)) = (a / d * f · + b / d) := by
      grind [Pi.div_apply]
    rw [this]
    clear this
    have s1 := isBigO_characteristic_sub_characteristic_shift (a₀ := (b / d : ℂ))
      (f := fun z ↦ a / d * f z + b / d) (by fun_prop)
    rw [show (fun z ↦ (a / d * f z + b / d) - b / d) = (fun z ↦ a / d * f z) by funext z; ring]
      at s1
    have s2 := isBigO_characteristic_sub_characteristic_const_mul (f := f) (s := a / d) hf
      (div_ne_zero hΔ.1 hΔ.2)
    have keyC : (characteristic (fun z ↦ a / d * f z + b / d) ⊤ - characteristic f ⊤)
        = (characteristic (fun z ↦ a / d * f z + b / d) ⊤ - characteristic (fun z ↦ a / d * f z)
            ⊤)
          + (characteristic (fun z ↦ a / d * f z) ⊤ - characteristic f ⊤) := by
      ext r
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [keyC]
    exact s1.add s2
  · -- Case `c ≠ 0`.
    by_cases hord : ∀ z, meromorphicOrderAt (fun w ↦ c * f w + d) z ≠ ⊤
    · -- Generic case: the denominator `c * f + d` is not locally constant zero.
      have hmero_den : Meromorphic (fun z ↦ c * f z + d) := by fun_prop
      have hmeroOn : MeromorphicOn (fun z ↦ c * f z + d) Set.univ := hmero_den.meromorphicOn
      have hne : ∀ᶠ z in codiscrete ℂ, c * f z + d ≠ 0 :=
        MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero hmeroOn (fun u _ ↦ hord u)
      -- The composite agrees, away from a codiscrete set, with the generator form
      -- `a / c + λ * (f + d / c)⁻¹`, where `λ = (b * c - a * d) / c ^ 2`.
      have hφeq : (fun z ↦ (a * f z + b) / (c * f z + d)) =ᶠ[codiscrete ℂ]
          (fun z ↦ a / c + (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) := by
        filter_upwards [hne] with z hz
        have hfk : f z + d / c ≠ 0 := by
          rw [show f z + d / c = (c * f z + d) / c by field_simp]
          exact div_ne_zero hz hc
        have hz' : f z * c + d ≠ 0 := by rw [mul_comm (f z) c]; exact hz
        field_simp [hc, hz, hz', hfk]
        ring
      have hcod : characteristic (fun z ↦ (a * f z + b) / (c * f z + d)) ⊤
          =ᶠ[atTop] characteristic (fun z ↦ a / c + (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) ⊤
            := by
        filter_upwards [eventually_ne_atTop (0 : ℝ)] with r hr
        exact characteristic_congr_codiscrete hφeq hr
      -- The constant `λ` is nonzero.
      have hl : (b * c - a * d) / c ^ 2 ≠ 0 :=
        div_ne_zero (fun h ↦ hΔ (by linear_combination -h)) (pow_ne_zero 2 hc)
      -- The four generator steps.
      have d4 : (characteristic (fun z ↦ f z + d / c) ⊤ - characteristic f ⊤)
          =O[atTop] (1 : ℝ → ℝ) := by
        have s4 := isBigO_characteristic_sub_characteristic_shift (a₀ := (-(d / c) : ℂ)) (f := f) hf
        rw [show (fun z ↦ f z - -(d / c)) = (fun z ↦ f z + d / c) by funext z; ring] at s4
        exact flip s4
      have d3 : (characteristic (fun z ↦ (f z + d / c)⁻¹) ⊤
          - characteristic (fun z ↦ f z + d / c) ⊤) =O[atTop] (1 : ℝ → ℝ) := by
        have s3 := isBigO_characteristic_sub_characteristic_inv
          (f := fun z ↦ f z + d / c) (by fun_prop)
        rw [show (fun z ↦ f z + d / c)⁻¹ = (fun z ↦ (f z + d / c)⁻¹) by funext z; simp] at s3
        exact flip s3
      have d2 : (characteristic (fun z ↦ (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) ⊤
          - characteristic (fun z ↦ (f z + d / c)⁻¹) ⊤) =O[atTop] (1 : ℝ → ℝ) :=
        isBigO_characteristic_sub_characteristic_const_mul
          (f := fun z ↦ (f z + d / c)⁻¹) (s := (b * c - a * d) / c ^ 2) (by fun_prop) hl
      have d1 : (characteristic (fun z ↦ a / c + (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) ⊤
          - characteristic (fun z ↦ (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) ⊤)
          =O[atTop] (1 : ℝ → ℝ) := by
        have s1 := isBigO_characteristic_sub_characteristic_shift (a₀ := (a / c : ℂ))
          (f := fun z ↦ a / c + (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) (by fun_prop)
        rw [show (fun z ↦ (a / c + (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) - a / c)
          = (fun z ↦ (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) by funext z; ring] at s1
        exact s1
      -- Telescope the four steps.
      have chain : (characteristic (fun z ↦ a / c + (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) ⊤
          - characteristic f ⊤) =O[atTop] (1 : ℝ → ℝ) := by
        have key : (characteristic (fun z ↦ a / c + (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) ⊤
            - characteristic f ⊤)
            = (((characteristic (fun z ↦ a / c + (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) ⊤
                - characteristic (fun z ↦ (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) ⊤)
              + (characteristic (fun z ↦ (b * c - a * d) / c ^ 2 * (f z + d / c)⁻¹) ⊤
                - characteristic (fun z ↦ (f z + d / c)⁻¹) ⊤))
              + (characteristic (fun z ↦ (f z + d / c)⁻¹) ⊤
                - characteristic (fun z ↦ f z + d / c) ⊤))
              + (characteristic (fun z ↦ f z + d / c) ⊤ - characteristic f ⊤) := by
          ext r; simp only [Pi.add_apply, Pi.sub_apply]; ring
        rw [key]
        exact ((d1.add d2).add d3).add d4
      -- Transport along the codiscrete agreement.
      exact chain.congr' (hcod.symm.sub EventuallyEq.rfl) EventuallyEq.rfl
    · -- Degenerate case: the denominator vanishes away from a codiscrete set.
      have hmero_den : Meromorphic (fun z ↦ c * f z + d) := by fun_prop
      have hNotEx : ¬ ∃ x, meromorphicOrderAt (fun w ↦ c * f w + d) x ≠ ⊤ := by
        rw [hmero_den.exists_meromorphicOrderAt_ne_top_iff_forall]; exact hord
      have hAllTop : ∀ z, meromorphicOrderAt (fun w ↦ c * f w + d) z = ⊤ := by
        intro z; by_contra hz; exact hNotEx ⟨z, hz⟩
      have hzero : (fun z ↦ c * f z + d) =ᶠ[codiscrete ℂ] 0 := by
        have hmem : {z : ℂ | c * f z + d = 0} ∈ codiscrete ℂ := by
          rw [Filter.codiscrete, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
          intro x _
          rw [Set.compl_univ, Set.union_empty]
          exact meromorphicOrderAt_eq_top_iff.1 (hAllTop x)
        filter_upwards [hmem] with z hz using hz
      have hfconst : f =ᶠ[codiscrete ℂ] (fun _ ↦ -(d / c)) := by
        filter_upwards [hzero] with z hz
        have hz' : c * f z + d = 0 := hz
        field_simp
        linear_combination hz'
      have hφ0 : (fun z ↦ (a * f z + b) / (c * f z + d)) =ᶠ[codiscrete ℂ] (fun _ ↦ (0 : ℂ)) := by
        filter_upwards [hzero] with z hz
        have hz' : c * f z + d = 0 := hz
        rw [show c * f z + d = 0 from hz', div_zero]
      have hcharf : characteristic f ⊤ =O[atTop] (1 : ℝ → ℝ) :=
        (characteristic_isBigO_one_iff_constant hf.meromorphicOn).1
          (eventuallyConst_iff_exists_eventuallyEq.2 ⟨-(d / c), hfconst⟩)
      have hcharφf : characteristic (fun z ↦ (a * f z + b) / (c * f z + d)) ⊤
          =O[atTop] (1 : ℝ → ℝ) :=
        (characteristic_isBigO_one_iff_constant
          ((by fun_prop : Meromorphic (fun z ↦ (a * f z + b) / (c * f z + d))).meromorphicOn)).1
          (eventuallyConst_iff_exists_eventuallyEq.2 ⟨0, hφ0⟩)
      exact hcharφf.sub hcharf

end ValueDistribution
