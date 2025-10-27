import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.Complex.ValueDistribution.CountingFunction
import Mathlib.RingTheory.LocalRing.Basic

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

namespace ValueDistribution

variable [ProperSpace 𝕜]

/--
For natural numbers `n`, the counting function counting zeros of `f ^ n` equals
`n` times the counting function counting zeros of `f`.
-/
@[simp] theorem logCounting_pow_zero {f : 𝕜 → 𝕜} {n : ℕ} (hf : MeromorphicOn f Set.univ) :
    logCounting (f ^ n) 0 = n • logCounting f 0 := by
  simp [logCounting, divisor_fun_pow hf n]

/--
For natural numbers `n`, the counting function counting poles of `f ^ n` equals
`n` times the counting function counting poles of `f`.
-/
@[simp] theorem logCounting_pow_top {f : 𝕜 → 𝕜} {n : ℕ} (hf : MeromorphicOn f Set.univ) :
    logCounting (f ^ n) ⊤ = n • logCounting f ⊤ := by
  simp [logCounting, divisor_pow hf n]


end ValueDistribution
