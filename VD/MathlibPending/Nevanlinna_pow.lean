import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import VD.MathlibSubmitted.PosLog

open MeromorphicOn Real

namespace ValueDistribution

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]

/--
For natural numbers `n`, the proximity function of `f ^ n` at `⊤` equals `n`
times the proximity function of `f` at `⊤`.
-/
@[simp] theorem proximity_pow_top {f : ℂ → ℂ} {n : ℕ} :
    proximity (f ^ n) ⊤ = n • (proximity f ⊤) := by
  simp only [proximity, reduceDIte, Pi.pow_apply, norm_pow, posLog_pow, nsmul_eq_mul]
  ext _
  rw [Pi.mul_apply, Pi.natCast_apply, ← smul_eq_mul, ← circleAverage_fun_smul]
  rfl

/--
For natural numbers `n`, the proximity function of `f ^ n` at `0` equals `n`
times the proximity function of `f` at `0`.
-/
@[simp] theorem proximity_pow_zero {f : ℂ → ℂ} {n : ℕ} :
    proximity (f ^ n) 0 = n • (proximity f 0) := by
  rw [← proximity_inv, ← proximity_inv, (by aesop : (f ^ n)⁻¹ = f⁻¹ ^ n), proximity_pow_top]

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

/--
For natural numbers `n`, the counting function counting zeros of `f ^ n` equals
`n` times the counting function counting zeros of `f`.
-/
@[simp] theorem characteristic_pow_zero {f : ℂ → ℂ} {n : ℕ} (hf : MeromorphicOn f Set.univ) :
    characteristic (f ^ n) 0 = n • characteristic f 0 := by
  simp_all [characteristic]

/--
For natural numbers `n`, the counting function counting poles of `f ^ n` equals
`n` times the counting function counting poles of `f`.
-/
@[simp] theorem characteristic_pow_top {f : ℂ → ℂ} {n : ℕ} (hf : MeromorphicOn f Set.univ) :
    characteristic (f ^ n) ⊤ = n • characteristic f ⊤ := by
  simp_all [characteristic]

end ValueDistribution
