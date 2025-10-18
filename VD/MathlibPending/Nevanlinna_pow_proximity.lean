import Mathlib.Analysis.Complex.ValueDistribution.ProximityFunction
import VD.MathlibSubmitted.PosLog

open Real

namespace ValueDistribution

/--
For natural numbers `n`, the counting function counting poles of `f ^ n` equals
`n` times the counting function counting poles of `f`.
-/
@[simp] theorem proximity_pow_top {f : ℂ → ℂ} {n : ℕ} :
    proximity (f ^ n) ⊤ = n • (proximity f ⊤) := by
  simp only [proximity, reduceDIte, Pi.pow_apply, norm_pow, posLog_pow, nsmul_eq_mul]
  ext _
  rw [Pi.mul_apply, Pi.natCast_apply, ← smul_eq_mul, ← circleAverage_fun_smul]
  rfl

/--
For natural numbers `n`, the counting function counting zeros of `f ^ n` equals
`n` times the counting function counting zeros of `f`.
-/
@[simp] theorem proximity_pow_zero {f : ℂ → ℂ} {n : ℕ} :
    proximity (f ^ n) 0 = n • (proximity f 0) := by
  rw [← proximity_inv, ← proximity_inv, (by aesop : (f ^ n)⁻¹ = f⁻¹ ^ n), proximity_pow_top]

end ValueDistribution
