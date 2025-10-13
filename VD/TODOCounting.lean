import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Analysis.Complex.ValueDistribution.CountingFunction
import Mathlib.Analysis.Complex.ValueDistribution.ProximityFunction

open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

theorem finsum_le_finsum
    {α R : Type*} [AddCommMonoid R] [LinearOrder R] [AddLeftMono R]
    (f₁ f₂ : α → R) (hf : f₁ ≤ f₂) (hf₁ : f₁.support.Finite) (hf₂ : f₂.support.Finite) :
    ∑ᶠ (a : α), f₁ a ≤ ∑ᶠ (a : α), f₂ a := by
  rw [finsum_eq_sum_of_support_subset f₁ (by simp : f₁.support ⊆ (hf₁.toFinset ∪ hf₂.toFinset : Finset α))]
  rw [finsum_eq_sum_of_support_subset f₂ (by simp : f₂.support ⊆ (hf₁.toFinset ∪ hf₂.toFinset : Finset α))]
  exact Finset.sum_le_sum fun a _ ↦ hf a

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

namespace Function.locallyFinsuppWithin

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*} [AddCommGroup Y] [LinearOrder Y]

instance x [IsOrderedAddMonoid Y] : IsOrderedAddMonoid (Function.locallyFinsuppWithin U Y) where
  add_le_add_left _ _ h _ x := by simp [h x]

theorem posPart_le
    {f₁ f₂ : Function.locallyFinsuppWithin U Y} (h : f₁ ≤ f₂):
    f₁⁺ ≤ f₂⁺ := by
  intro x
  by_cases hf : f₁ x ≤ 0
  · simp [instPosPart, hf]
  · simp [instPosPart, h x, (lt_of_lt_of_le (not_le.1 hf) (h x)).le]

theorem negPart_le [IsOrderedAddMonoid Y]
    {f₁ f₂ : Function.locallyFinsuppWithin U Y} (h : f₁ ≤ f₂):
    f₂⁻ ≤ f₁⁻ := by
  intro x
  by_cases hf : -f₁ x ≤ 0
  · simp_all only [Left.neg_nonpos_iff, instNegPart, max_apply, coe_neg, Pi.neg_apply, coe_zero,
      Pi.zero_apply, sup_of_le_right, sup_le_iff, le_refl, and_true]
    exact Std.IsPreorder.le_trans 0 (f₁ x) (f₂ x) hf (h x)
  · rw [Left.neg_nonpos_iff, not_le] at hf
    simp_all [instNegPart, h x, hf.le]

theorem evenlogCounting (f : locallyFinsuppWithin (univ : Set E) ℤ) :
    (logCounting f).Even := by
  intro r
  simp [logCounting, toClosedBall]
  rw [abs_neg r]

end Function.locallyFinsuppWithin


/--
The order of a constant function is `⊤` is the the constant is zero and `0` otherwise.
-/
theorem meromorphicOrderAt_const (z₀ : 𝕜) (e : E) :
    meromorphicOrderAt (fun _ ↦ e) z₀ = if e = 0 then ⊤ else (0 : WithTop ℤ) := by
  by_cases he : e = 0
  · simp [he, meromorphicOrderAt_eq_top_iff]
  simp [he]
  rw [(by rfl : (0 : WithTop ℤ) = (0 : ℤ)), meromorphicOrderAt_eq_int_iff (MeromorphicAt.const e z₀)]
  use fun _ ↦ e
  simp [he]
  fun_prop

/--
Variant of `meromorphicOrderAt_const`, for constant functions defined by
coercion from natural numbers.
-/
theorem meromorphicOrderAt_const_ofNat (z₀ : 𝕜) (n : ℤ) :
    meromorphicOrderAt (n : 𝕜 → 𝕜) z₀ = if (n : 𝕜) = 0 then ⊤ else (0 : WithTop ℤ) := by
  apply meromorphicOrderAt_const

/--
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
theorem divisor_pow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℕ) :
    divisor (f ^ n) U = n • divisor f U := by
  ext z
  by_cases hn : n = 0
  · simp only [hn, pow_zero, divisor_def, zero_nsmul, Function.locallyFinsuppWithin.coe_zero,
      Pi.zero_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero, and_imp]
    intro _ _
    have := meromorphicOrderAt_const_ofNat z 1
    simp_all
  by_cases hz : ¬z ∈ U
  · simp [hz]
  simp_all only [Decidable.not_not, hf.pow n, divisor_apply,
    Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply, Int.nsmul_eq_mul]
  rw [meromorphicOrderAt_pow (hf z hz)]
  aesop

/--
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
theorem divisor_fun_pow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℕ) :
    divisor (fun z ↦ f z ^ n) U = n • divisor f U := divisor_pow hf n

/--
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
theorem divisor_zpow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℤ) :
    divisor (f ^ n) U = n • divisor f U := by
  ext z
  by_cases hn : n = 0
  · simp only [hn, zpow_zero, divisor_def, zero_smul, Function.locallyFinsuppWithin.coe_zero,
      Pi.zero_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero, and_imp]
    intro _ _
    have := meromorphicOrderAt_const_ofNat z 1
    simp_all
  by_cases hz : ¬z ∈ U
  · simp [hz]
  simp_all only [Decidable.not_not, hf.zpow n, divisor_apply,
    Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, Int.zsmul_eq_mul]
  rw [meromorphicOrderAt_zpow (hf z hz)]
  aesop

/--
If `f` is meromorphic, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
theorem divisor_fun_zpow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℤ) :
    divisor (fun z ↦ f z ^ n) U = n • divisor f U := divisor_zpow hf n

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
    simp only [map_zsmul, coe_zsmul, Pi.smul_apply, eq_intCast, Int.cast_eq]
    ext r
    rw [Pi.smul_apply, smul_add, smul_finsum]
    congr 1
    · congr 1
      ext z
      rw [smul_eq_mul, Int.cast_mul]
      ring
    · rw [smul_eq_mul, Int.cast_mul]
      ring

end Function.locallyFinsuppWithin

namespace ValueDistribution

variable [ProperSpace 𝕜]

variable (f a) in
noncomputable def logCounting' : ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact (divisor f univ)⁻.logCounting'
  · exact (divisor (fun z ↦ f z - a.untop₀) univ)⁺.logCounting'


theorem posPart_add
    {X : Type*} [TopologicalSpace X] {U : Set X}
    {Y : Type*} [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]
    (f₁ f₂ : Function.locallyFinsuppWithin U Y) :
    (f₁ + f₂)⁺ ≤ f₁⁺ + f₂⁺ := by
  unfold instPosPart
  rw [Function.locallyFinsuppWithin.le_def]
  intro x
  simp only [Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.coe_add,
    Pi.add_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor
  · simp [add_le_add]
  · simp [add_nonneg]

theorem negPart_add
    {X : Type*} [TopologicalSpace X] {U : Set X}
    {Y : Type*} [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]
    (f₁ f₂ : Function.locallyFinsuppWithin U Y) :
    (f₁ + f₂)⁻ ≤ f₁⁻ + f₂⁻ := by
  unfold instNegPart
  rw [Function.locallyFinsuppWithin.le_def]
  intro x
  simp only [neg_add_rev, Function.locallyFinsuppWithin.max_apply,
    Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_neg, Pi.add_apply,
    Pi.neg_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor
  · simp [add_comm, add_le_add]
  · simp [add_nonneg]

/--
Taking the positive part of a function with locally finite support commutes with
scalar multiplication by a natural number.
-/
theorem nsmul_posPart
    {X : Type*} [TopologicalSpace X] {U : Set X}
    {Y : Type*} [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]
    (f : Function.locallyFinsuppWithin U Y) (n : ℕ) :
    n • f⁺ = (n • f)⁺ := by
  unfold instPosPart
  ext x
  simp only [Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  by_cases h : f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

/--
Taking the negative part of a function with locally finite support commutes with
scalar multiplication by a natural number.
-/
theorem nsmul_negPart
    {X : Type*} [TopologicalSpace X] {U : Set X}
    {Y : Type*} [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]
    (f : Function.locallyFinsuppWithin U Y) (n : ℕ) :
    n • f⁻ = (n • f)⁻ := by
  unfold instNegPart
  ext x
  simp only [Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply,
    Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  by_cases h : -f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

/--
For natural numbers `n`, the counting function counting zeros of `f ^ n` equals
`n` times the counting function counting zeros of `f`.
-/
@[simp] theorem logCounting_pow_zero {f : 𝕜 → 𝕜} {n : ℕ} (hf : MeromorphicOn f Set.univ) :
    logCounting' (f ^ n) 0 = n • logCounting' f 0 := by
  simp [logCounting', divisor_fun_pow hf n, ← nsmul_posPart]

/--
For natural numbers `n`, the counting function counting poles of `f ^ n` equals
`n` times the counting function counting poles of `f`.
-/
@[simp] theorem logCounting_pow_top {f : 𝕜 → 𝕜} {n : ℕ} (hf : MeromorphicOn f Set.univ) :
    logCounting' (f ^ n) ⊤ = n • logCounting' f ⊤ := by
  simp [logCounting', divisor_pow hf n, ← nsmul_negPart]

/--
For natural numbers `n`, the counting function counting zeros of `f ^ n` equals
`n` times the counting function counting zeros of `f`.
-/
@[simp] theorem logCounting_mul {f₁ f₂ : 𝕜 → 𝕜} (hf₁ : MeromorphicOn f₁ Set.univ) (hf₂ : MeromorphicOn f₂ Set.univ) :
    logCounting' (f₁ * f₂) 0 ≤ logCounting' f₁ 0 + logCounting' f₂ 0 := by
  unfold logCounting'
  simp only [WithTop.zero_ne_top, ↓reduceDIte, WithTop.untop₀_zero, sub_zero]
  rw [divisor_mul hf₁ hf₂]
  rw [← Function.locallyFinsuppWithin.logCounting'.map_add]
  simp
  sorry


end ValueDistribution
