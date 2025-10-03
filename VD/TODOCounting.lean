import Mathlib.Analysis.Complex.ValueDistribution.CountingFunction

open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

lemma test (a : 𝕜) (n : ℕ) :
    ‖n * a + a‖ ≤ ‖n * a‖ + ‖a‖ := by
  calc ‖n * a + a‖
  _ = dist (n * a + a) 0 := by
    rw [NormedField.dist_eq]
    simp
  _ ≤ dist (n * a + a) a + dist a 0 := by
    apply dist_triangle
  _ ≤ ‖n * a‖ + ‖a‖ := by
    rw [NormedField.dist_eq]
    rw [NormedField.dist_eq]
    simp

lemma xx (a : 𝕜) (n : ℕ) :
    ‖n * a‖ ≤ n * ‖a‖ := by
  induction n with
  | zero =>
    simp
  | succ m hm =>
    rw [Nat.cast_add_one m]
    rw [Nat.cast_add_one m]
    calc ‖(m + 1) * a‖
    _ = ‖m * a + a‖ := by
      congr
      ring
    _ ≤ ‖m * a‖ + ‖a‖ := by
      exact test a m
    _ ≤ m * ‖a‖ + ‖a‖ := by
      exact add_le_add_right hm ‖a‖
    _ ≤ (m + 1) * ‖a‖ := by
      ring_nf
      simp

lemma zz (n : ℕ) :
    (n : 𝕜) = 0 ↔ n = 0 := by
  constructor
  · intro hn
    by_contra hCon
    have : ‖(n : 𝕜)‖ \
    sorry
  · simp_all


theorem mul_finsum'
    {α : Type u_1} {R : Type u_7} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R]
    (f : α → R) (r : R) :
    r * ∑ᶠ (a : α), f a = ∑ᶠ (a : α), r * f a := by
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact mul_finsum f r h
  · simp [finsum_def, h, (by aesop : (r * f ·).support = f.support)]

namespace MeromorphicOn

theorem meromorphicOrderAt_const (z₀ : 𝕜) (e : E) :
    meromorphicOrderAt (fun _ ↦ e) z₀ = if e = 0 then ⊤ else (0 : WithTop ℤ) := by
  by_cases he : e = 0
  · simp [he, meromorphicOrderAt_eq_top_iff]
  simp [he]
  rw [(by rfl : (0 : WithTop ℤ) = (0 : ℤ)), meromorphicOrderAt_eq_int_iff (MeromorphicAt.const e z₀)]
  use fun _ ↦ e
  simp [he]
  fun_prop

theorem meromorphicOrderAt_const_ofNat (z₀ : 𝕜) (n : ℤ) :
    meromorphicOrderAt (n : 𝕜 → 𝕜) z₀ = if (n : 𝕜) = 0 then ⊤ else (0 : WithTop ℤ) := by
  apply meromorphicOrderAt_const

theorem divisor_pow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℕ) :
    divisor (f ^ n) U = n • divisor f U := by
  ext z
  by_cases hn : n = 0
  · simp [hn, divisor_def]
    intro h₂f hz
    have := meromorphicOrderAt_const_ofNat z 1
    simp_all
  by_cases hz : ¬z ∈ U
  · simp [hz]
  simp_all [hf.pow n]
  rw [meromorphicOrderAt_pow]
  aesop
  exact hf z hz

theorem divisor_pow' {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℕ) :
    divisor (fun z ↦ f z ^ n) U = n • divisor f U := by
  apply divisor_pow hf

theorem divisor_zpow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℤ) :
    divisor (f ^ n) U = n • divisor f U := by
  ext z
  by_cases hn : n = 0
  · simp [hn, divisor_def]
    intro h₂f hz
    left
    -- should be automatic from here
    have XX := meromorphicOrderAt_eq_int_iff (h₂f z hz) (n := 0)
    have YY : (0 : WithTop ℤ) = (0 : ℤ) := by
      rfl
    rw [YY, XX]
    use 1
    simp
    apply analyticAt_const -- should work with fun_prop, but doesn't
  by_cases hz : ¬z ∈ U
  · simp [hz]
  simp_all [hf.zpow n]
  rw [meromorphicOrderAt_zpow]
  aesop
  exact hf z hz

theorem divisor_zpow' {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℤ) :
    divisor (fun z ↦ f z ^ n) U = n • divisor f U := by
  apply divisor_zpow hf

end MeromorphicOn

namespace Function.locallyFinsuppWithin

noncomputable def logCounting' {E : Type*} [NormedAddCommGroup E] [ProperSpace E] :
    locallyFinsuppWithin (univ : Set E) ℤ →ₗ[ℤ] (ℝ → ℝ) where
  toFun D := fun r ↦ ∑ᶠ z, D.toClosedBall r z * log (r * ‖z‖⁻¹) + (D 0) * log r
  map_add' D₁ D₂ := by
    simp only [map_add, coe_add, Pi.add_apply, Int.cast_add]
    ext r
    have {A B C D : ℝ} : A + B + (C + D) = A + C + (B + D) := by ring
    rw [Pi.add_apply, this]
    congr 1
    · have h₁s : ((D₁.toClosedBall r).support ∪ (D₂.toClosedBall r).support).Finite := by
        apply Set.finite_union.2
        constructor
        <;> apply finiteSupport _ (isCompact_closedBall 0 |r|)
      repeat
        rw [finsum_eq_sum_of_support_subset (s := h₁s.toFinset)]
        try simp_rw [← Finset.sum_add_distrib, ← add_mul]
      repeat
        intro x hx
        by_contra
        simp_all
    · ring
  map_smul' n D := by
    simp
    ext r
    simp
    rw [mul_add, mul_finsum']
    congr 1
    · congr 1
      ext z
      ring
    · ring

end Function.locallyFinsuppWithin

namespace ValueDistribution

variable [ProperSpace 𝕜]

variable (f a) in
noncomputable def logCounting' : ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact (divisor f univ)⁻.logCounting'
  · exact (divisor (fun z ↦ f z - a.untop₀) univ)⁺.logCounting'

@[simp] theorem logCounting_pow_zero {f : 𝕜 → 𝕜} {n : ℕ} (hf : MeromorphicOn f Set.univ) :
    logCounting' (f ^ n) 0 = n • logCounting' f 0 := by

  unfold logCounting'
  simp only [WithTop.zero_ne_top, ↓reduceDIte, Pi.pow_apply, WithTop.untop₀_zero, sub_zero]
  rw [divisor_pow' hf n]
  have : (n • divisor f univ)⁺ = n • (divisor f univ)⁺ := by
    unfold posPart
    unfold instPosPart
    simp
    ext z
    simp
    have {a : ℤ} {b : ℕ} : max (n * a) 0 = n * (max a 0) := by
      by_cases h : 0 < a
      · simp [h]
        left
        exact Int.le_of_lt h
      · simp at h
        simp [h]
        apply Int.mul_nonpos_of_nonneg_of_nonpos
        exact Int.natCast_nonneg n
        exact h
    apply this
    exact 1
  rw [this]
  have : (n • (divisor f univ)⁺) = ((n : ℤ) • (divisor f univ)⁺) := rfl
  rw [this]
  rw [Function.locallyFinsuppWithin.logCounting'.map_smul n (divisor f univ)⁺]
  simp

/-
@[simp] theorem logCounting_pow_top {f : 𝕜 → 𝕜} {n : ℕ} (hf : MeromorphicOn f Set.univ) :
    logCounting' (f ^ n) ⊤ = n • logCounting' f ⊤ := by
  sorry
-/

end ValueDistribution
