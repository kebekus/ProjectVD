import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.Complex.ValueDistribution.CountingFunction
import Mathlib.RingTheory.LocalRing.Basic
import VD.MathlibSubmitted.DivisorOrder

open MeromorphicOn Metric Real Set Classical Function.locallyFinsuppWithin

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}


namespace MeromorphicOn

/--
The order of a constant function is `⊤` if the the constant is zero and `0` otherwise.
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
The divisor of a constant function is `0`.
-/
@[simp]
theorem divisor_const (e : E) :
    divisor (fun _ ↦ e) U = 0 := by
  classical
  ext x
  simp only [divisor_def, meromorphicOrderAt_const, Function.locallyFinsuppWithin.coe_zero,
    Pi.zero_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero,
    LinearOrderedAddCommGroupWithTop.top_ne_zero, imp_false, ite_eq_left_iff, WithTop.zero_ne_top,
    Decidable.not_not, and_imp]
  tauto

/--
The divisor of a constant function is `0`.
-/
@[simp]
theorem divisor_intCast (n : ℤ) :
    divisor (n : 𝕜 → 𝕜) U = 0 := divisor_const (n : 𝕜)

/--
The divisor of a constant function is `0`.
-/
@[simp]
theorem divisor_natCast (n : ℕ) :
    divisor (n : 𝕜 → 𝕜) U = 0 := divisor_const (n : 𝕜)

/--
The divisor of a constant function is `0`.
-/
@[simp] theorem divisor_ofNat (n : ℕ) :
    divisor (ofNat(n) : 𝕜 → 𝕜) U = 0 := by
  convert divisor_const (n : 𝕜)
  simp [Semiring.toGrindSemiring_ofNat 𝕜 n]

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

end ValueDistribution
