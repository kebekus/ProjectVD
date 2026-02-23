import Mathlib.Analysis.Meromorphic.FactorizedRational

set_option backward.isDefEq.respectTransparency false

open Complex ComplexConjugate Real

variable {R : ℝ} {w : ℂ}

/-- The order is additive when multiplying meromorphic functions. -/
theorem meromorphicOrderAt_fun_mul {f g : ℂ → ℂ} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    meromorphicOrderAt (fun z ↦ f z * g z) x = meromorphicOrderAt f x + meromorphicOrderAt g x :=
  meromorphicOrderAt_smul hf hg

theorem meromorphicOrderAt_fun_inv {f : ℂ → ℂ} :
    meromorphicOrderAt (fun z ↦ (f z)⁻¹) x = -meromorphicOrderAt f x := by
  exact meromorphicOrderAt_inv

@[to_fun]
theorem meromorphicOrderAt_div {x : ℂ} {f g : ℂ → ℂ}  (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f / g) x = meromorphicOrderAt f x - meromorphicOrderAt g x := by
  rw [div_eq_mul_inv, meromorphicOrderAt_mul hf hg.inv, meromorphicOrderAt_inv, sub_eq_add_neg]

theorem meromorphicOrderAt_id_sub_const {w : ℂ} :
    meromorphicOrderAt (· - w) w = 1 := by
  rw [(by rfl : (1 : WithTop ℤ) = (1 : ℤ)), meromorphicOrderAt_eq_int_iff (by fun_prop) (n := 1)]
  use fun z ↦ 1, by fun_prop, one_ne_zero
  aesop

@[to_fun]
theorem meromorphicOrderAt_zpow_id_sub_const {w : ℂ} {n : ℤ} :
    meromorphicOrderAt ((· - w) ^ n) w = n := by
  rw [meromorphicOrderAt_zpow (by fun_prop), meromorphicOrderAt_id_sub_const, mul_one]
