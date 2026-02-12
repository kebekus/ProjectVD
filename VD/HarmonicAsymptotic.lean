import VD.MathlibPending.ComplexMeanvalue_2

open Asymptotics Classical Complex ComplexConjugate Filter Function Metric Real Set Classical Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}

theorem testCase₃ {φ θ : ℝ} {r R : ℝ} (h₁ : 0 < r) (h₂ : r < R) :
    ( (R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I)) ).re
    ≤ (R + r) / (R - r) := by
  rw [ div_eq_mul_inv ]
  -- Realize that $Real.cos(θ - φ) ≤ 1$, and thus $R^2 + r^2 - 2 * R * r * Real.cos(θ - φ) ≥ (R - r)^2$.
  have h_cos : (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) ≥ (R - r) ^ 2 := by
    nlinarith [ mul_pos h₁ ( sub_pos.mpr h₂ ), Real.cos_le_one ( θ - φ ) ]
  -- Substitute the simplified expression back into the inequality.
  have h_subst : (R^2 - r^2) / (R^2 + r^2 - 2 * R * r * Real.cos (θ - φ)) ≤ (R + r) / (R - r) := by
    rw [ div_le_div_iff₀ ]
    <;> nlinarith [ mul_pos h₁ ( sub_pos.mpr h₂ ) ]
  convert h_subst using 1
  norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im ]
  ring_nf
  norm_num [ Real.sin_sq, Real.cos_sq ]
  ring_nf
  rw [ Real.cos_sub ]
  ring

theorem testCase₄ {φ θ : ℝ} {r R : ℝ} (h₁ : 0 < r) (h₂ : r < R) :
    (R - r) / (R + r)
    ≤ ( (R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I)) ).re := by
  norm_num [ Complex.normSq, Complex.div_re ]
  rw [ ← add_div, div_le_div_iff₀ ]
  · ring_nf
    norm_num [ Real.sin_sq, Real.cos_sq ]
    ring_nf
    nlinarith [ mul_le_mul_of_nonneg_left
      ( show Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ ≤ 1 by nlinarith only [ sq_nonneg ( Real.cos θ * Real.sin φ - Real.sin θ * Real.cos φ ), Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ ] )
      ( show 0 ≤ R * r by nlinarith ), mul_le_mul_of_nonneg_left
        ( show Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ ≥ -1 by nlinarith only [ sq_nonneg ( Real.cos θ * Real.sin φ - Real.sin θ * Real.cos φ ), Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ ] )
        ( show 0 ≤ R * r by nlinarith ) ]
  · linarith
  · -- Expanding the squares and simplifying, we get:
    have h_expand : (R * Real.cos θ - r * Real.cos φ) * (R * Real.cos θ - r * Real.cos φ) + (R * Real.sin θ - r * Real.sin φ) * (R * Real.sin θ - r * Real.sin φ) = R^2 + r^2 - 2 * R * r * Real.cos (θ - φ) := by
      rw [ Real.cos_sub ]
      nlinarith [ Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ ]
    nlinarith [ mul_pos h₁ ( sub_pos.mpr h₂ ), Real.cos_le_one ( θ - φ ) ]
