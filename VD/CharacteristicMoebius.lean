/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import VD.MathlibPending.BoundednessCharacteristic

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

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

@[simp] theorem meromorphicAt_const_smul_iff_meromorphicAt {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicAt (s • f) z ↔ MeromorphicAt f z := by
  constructor
  <;> intro hf
  · rw [((eq_inv_smul_iff₀ hs).mpr rfl : f = s⁻¹ • s • f)]
    fun_prop
  · fun_prop

@[simp] theorem meromorphicAt_fun_const_smul_iff_meromorphicAt {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicAt (fun x ↦ s • f x) z ↔ MeromorphicAt f z :=
  meromorphicAt_const_smul_iff_meromorphicAt hs

@[simp] theorem meromorphicOn_const_smul_iff_meromorphicOn {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicOn (s • f) U ↔ MeromorphicOn f U :=
  ⟨fun hf x hx ↦ (meromorphicAt_fun_const_smul_iff_meromorphicAt hs).mp (hf x hx),
    fun hf x hx ↦ (meromorphicAt_const_smul_iff_meromorphicAt hs).mpr (hf x hx)⟩

@[simp] theorem meromorphicOn_fun_const_smul_iff_meromorphicOn {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicOn (fun x ↦ s • f x) U ↔ MeromorphicOn f U :=
  meromorphicOn_const_smul_iff_meromorphicOn hs

@[simp] theorem meromorphicOrderAt_const_smul_iff_meromorphicOrderAt {f : 𝕜 → E} {s : 𝕜}
    (hs : s ≠ 0) :
    meromorphicOrderAt (s • f) z = meromorphicOrderAt f z := by
  by_cases hf : MeromorphicAt f z
  · rw [(by aesop : s • f = (fun (_ : 𝕜) ↦ s) • f),
      meromorphicOrderAt_smul_of_ne_zero (by fun_prop) hs]
  simp_all

@[simp] theorem meromorphicOrderAt_fun_const_smul_iff_meromorphicOrderAt {f : 𝕜 → E} {s : 𝕜}
    (hs : s ≠ 0) :
    meromorphicOrderAt (fun x ↦ s • f x) z = meromorphicOrderAt f z :=
  meromorphicOrderAt_const_smul_iff_meromorphicOrderAt hs

@[simp] theorem divisor_const_smul {f : 𝕜 → E} {s : 𝕜} {U : Set 𝕜} (hs : s ≠ 0) :
    divisor (s • f) U = divisor f U := by
  ext z
  by_cases h₁f : MeromorphicOn f U
  · by_cases hz : z ∈ U
    · rw [divisor_apply h₁f hz, divisor_apply (by simp_all) hz]
      simp_all
    · simp_all
  · simp_all

@[simp] theorem divisor_fun_const_smul {f : 𝕜 → E} {s : 𝕜} {U : Set 𝕜} (hs : s ≠ 0) :
    divisor (fun x ↦ s • f x) U = divisor f U :=
  divisor_const_smul hs

@[simp] theorem logCounting_const_smul_top [ProperSpace 𝕜] {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    ValueDistribution.logCounting (s • f) ⊤ = ValueDistribution.logCounting f ⊤ := by
  simp_all [logCounting_top]

@[simp] theorem logCounting_fun_const_smul_top [ProperSpace 𝕜] {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    ValueDistribution.logCounting (fun x ↦ s • f x) ⊤ = ValueDistribution.logCounting f ⊤ :=
  logCounting_const_smul_top hs

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isBigO_proximity_top_sub_proximity_const_smul_top [ProperSpace 𝕜] {f : ℂ → E} {s : ℂ}
    (hs : s ≠ 0) :
    (proximity (s • f) ⊤ - proximity f ⊤) =O[atTop] (1 : ℝ → ℝ) := by
  have η₁ {r : ℝ} : proximity (s • f) ⊤ r ≤ log⁺ ‖s‖ + proximity f ⊤ r := by
    rw [show (s • f) = (fun _ : ℂ ↦ s) • f by funext z; rfl]
    sorry
  apply isBigO_of_le' (c := log⁺ ‖s‖ + log⁺ ‖s⁻¹‖)
  sorry

/--
Multiplying a meromorphic function by a nonzero constant changes the characteristic function (for
the value `⊤`) only by a bounded function: the logarithmic counting function is unchanged (the poles
are the same), and the proximity function changes by at most `log⁺ ‖l‖` resp. `log⁺ ‖l⁻¹‖`.
-/
theorem isBigO_characteristic_sub_characteristic_const_mul {g : ℂ → ℂ} {l : ℂ}
    (hg : Meromorphic g) (hl : l ≠ 0) :
    (characteristic (fun z ↦ l * g z) ⊤ - characteristic g ⊤) =O[atTop] (1 : ℝ → ℝ) := by
  -- The logarithmic counting functions agree, since the divisors agree.
  have hdiv : divisor (fun z ↦ l * g z) Set.univ = divisor g Set.univ := by
    ext z
    rw [divisor_apply ((show Meromorphic (fun z ↦ l * g z) by fun_prop).meromorphicOn)
        (Set.mem_univ z), divisor_apply hg.meromorphicOn (Set.mem_univ z)]
    congr 1
    rw [show (fun z ↦ l * g z) = (fun _ : ℂ ↦ l) • g by
        funext w; simp [smul_eq_mul],
      meromorphicOrderAt_smul (MeromorphicAt.const l z) (hg z)]
    simp [meromorphicOrderAt_const, hl]
  have hlog : logCounting (fun z ↦ l * g z) ⊤ = logCounting g ⊤ := by
    simp only [logCounting_top, hdiv]
  -- The proximity functions agree up to a bounded function.
  have hpx_le : ∀ r, proximity (fun z ↦ l * g z) ⊤ r ≤ log⁺ ‖l‖ + proximity g ⊤ r := by
    intro r
    rw [show (fun z ↦ l * g z) = (fun _ : ℂ ↦ l) * g by funext z; rfl]
    simpa [proximity_const] using (proximity_mul_top_le (Meromorphic.const l) hg) r
  have hpx_ge : ∀ r, proximity g ⊤ r ≤ log⁺ ‖l⁻¹‖ + proximity (fun z ↦ l * g z) ⊤ r := by
    intro r
    have hlg : Meromorphic (fun z ↦ l * g z) := by fun_prop
    have h2 := (proximity_mul_top_le (Meromorphic.const l⁻¹) hlg) r
    rw [show ((fun _ ↦ l⁻¹) * (fun z ↦ l * g z)) = g by
      funext z; simp [inv_mul_cancel_left₀ hl]] at h2
    simpa [proximity_const] using h2
  have hpx_bdd : ∀ r, ‖(proximity (fun z ↦ l * g z) ⊤ - proximity g ⊤) r‖
      ≤ (log⁺ ‖l‖ + log⁺ ‖l⁻¹‖) * ‖(1 : ℝ → ℝ) r‖ := by
    intro r
    simp only [Pi.sub_apply, Pi.one_apply, norm_one, mul_one, Real.norm_eq_abs, abs_le]
    refine ⟨?_, ?_⟩
    · linarith [hpx_ge r, posLog_nonneg (x := ‖l‖)]
    · linarith [hpx_le r, posLog_nonneg (x := ‖l⁻¹‖)]
  have hpx_isBigO : (proximity (fun z ↦ l * g z) ⊤ - proximity g ⊤) =O[atTop] (1 : ℝ → ℝ) :=
    isBigO_of_le' (c := log⁺ ‖l‖ + log⁺ ‖l⁻¹‖) _ hpx_bdd
  -- Combine: the characteristic difference equals the proximity difference.
  have hchar_eq : (characteristic (fun z ↦ l * g z) ⊤ - characteristic g ⊤)
      = (proximity (fun z ↦ l * g z) ⊤ - proximity g ⊤) := by
    unfold characteristic
    rw [hlog]
    ext r
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hchar_eq]
  exact hpx_isBigO

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
    (characteristic (fun z ↦ (a * f z + b) / (c * f z + d)) ⊤ - characteristic f ⊤)
      =O[atTop] (1 : ℝ → ℝ) := by
  -- A helper to reverse the order of a bounded difference.
  have flip : ∀ {A B : ℝ → ℝ}, (A - B) =O[atTop] (1 : ℝ → ℝ) → (B - A) =O[atTop] (1 : ℝ → ℝ) := by
    intro A B h
    have hAB : B - A = -(A - B) := by ext r; simp only [Pi.sub_apply, Pi.neg_apply]; ring
    rw [hAB]
    exact h.neg_left
  by_cases hc : c = 0
  · -- Affine case `c = 0`: the map is `w ↦ (a / d) * w + b / d`.
    have had : a * d ≠ 0 := by rw [hc] at hΔ; simpa using hΔ
    have ha : a ≠ 0 := left_ne_zero_of_mul had
    have hd : d ≠ 0 := right_ne_zero_of_mul had
    have hφeqC : (fun z ↦ (a * f z + b) / (c * f z + d)) = (fun z ↦ a / d * f z + b / d) := by
      funext z; rw [hc]; simp only [zero_mul, zero_add]; field_simp
    rw [hφeqC]
    have hg1C : Meromorphic (fun z ↦ a / d * f z + b / d) := by fun_prop
    have s1 := isBigO_characteristic_sub_characteristic_shift (a₀ := (b / d : ℂ))
      (f := fun z ↦ a / d * f z + b / d) hg1C
    rw [show (fun z ↦ (a / d * f z + b / d) - b / d) = (fun z ↦ a / d * f z) by funext z; ring]
      at s1
    have s2 := isBigO_characteristic_sub_characteristic_const_mul (g := f) (l := a / d) hf
      (div_ne_zero ha hd)
    have keyC : (characteristic (fun z ↦ a / d * f z + b / d) ⊤ - characteristic f ⊤)
        = (characteristic (fun z ↦ a / d * f z + b / d) ⊤ - characteristic (fun z ↦ a / d * f z)
            ⊤)
          + (characteristic (fun z ↦ a / d * f z) ⊤ - characteristic f ⊤) := by
      ext r; simp only [Pi.add_apply, Pi.sub_apply]; ring
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
          (g := fun z ↦ (f z + d / c)⁻¹) (l := (b * c - a * d) / c ^ 2) (by fun_prop) hl
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
