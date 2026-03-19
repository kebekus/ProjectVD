import Mathlib

open Complex Filter Metric Real MeasureTheory Set

/-!
# Dominated Convergence for Circle Averages

We prove that circle averages converge when the radius converges, provided
the hypotheses of the dominated convergence theorem are satisfied.

We then define the Herglotz–Riesz kernel and apply the general result to
the specific integrand `(re ∘ herglotzRieszKernel 0 w) • f`, where
`f z = log ‖z - ρ‖`, `‖ρ‖ = R`, and `‖w‖ < R`.
-/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **Dominated convergence for circle averages.**
If the integrand `g ∘ circleMap c (r n)` converges pointwise a.e. to `g ∘ circleMap c R`
and is dominated by an integrable function, then the circle averages converge. -/
theorem circleAverage_tendsto_of_tendsto_radius
    {g : ℂ → E} {c : ℂ} {R : ℝ}
    {r : ℕ → ℝ}
    (bound : ℝ → ℝ)
    (hbound : IntervalIntegrable bound volume 0 (2 * π))
    (hmeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (fun θ => g (circleMap c (r n) θ))
        (volume.restrict (uIoc 0 (2 * π))))
    (hdom : ∀ᶠ n in atTop,
      ∀ᵐ θ, θ ∈ uIoc 0 (2 * π) → ‖g (circleMap c (r n) θ)‖ ≤ bound θ)
    (hconv : ∀ᵐ θ, θ ∈ uIoc 0 (2 * π) →
      Tendsto (fun n => g (circleMap c (r n) θ)) atTop
        (nhds (g (circleMap c R θ)))) :
    Tendsto (fun n => circleAverage g c (r n)) atTop
      (nhds (circleAverage g c R)) := by
        refine' Filter.Tendsto.smul _ _
        · exact tendsto_const_nhds
        · have := @intervalIntegral.tendsto_integral_filter_of_dominated_convergence E
          specialize this bound hmeas hdom hbound hconv ; simpa using this

end General

/-!
## Herglotz–Riesz kernel
-/

/-- The integrand in our application: `Re((z + w)/(z - w)) · log ‖z - ρ‖`. -/
noncomputable def herglotzLogIntegrand (w ρ : ℂ) : ℂ → ℝ :=
  (Complex.re ∘ herglotzRieszKernel 0 w) • (fun z => Real.log ‖z - ρ‖)

/-!
## Helper lemmas for the specific convergence result
-/

/-
PROBLEM
Points on a circle of radius `r` centered at the origin have norm `|r|`.

PROVIDED SOLUTION
Unfold circleMap, use norm_mul, abs_ofReal, and Complex.norm_exp_ofReal_mul_I.
-/
lemma norm_circleMap_zero' (r : ℝ) (θ : ℝ) : ‖circleMap 0 r θ‖ = |r| := by
  norm_num [ circleMap ]

/-
PROBLEM
If `‖w‖ ≠ |r|`, then `circleMap 0 r θ ≠ w` for all `θ`.

PROVIDED SOLUTION
If circleMap 0 r θ = w then ‖w‖ = ‖circleMap 0 r θ‖ = |r|, contradicting h.
-/
lemma circleMap_zero_ne_of_norm_ne {w : ℂ} {r : ℝ} (h : ‖w‖ ≠ |r|) (θ : ℝ) :
    circleMap 0 r θ ≠ w := by
      unfold circleMap; aesop;

/-
PROBLEM
`herglotzLogIntegrand` is continuous at `z` provided `z ≠ w` and `z ≠ ρ`.

PROVIDED SOLUTION
herglotzLogIntegrand w ρ z = Re((z+w)/(z-w)) * log ‖z - ρ‖. The function z ↦ (z+w)/(z-w) is continuous at z ≠ w (the denominator z-w ≠ 0). Taking Re is continuous. The function z ↦ log ‖z - ρ‖ is continuous at z ≠ ρ (since ‖z - ρ‖ > 0 there). The product of two continuous-at functions is continuous-at.
-/
lemma herglotzLogIntegrand_continuousAt {w ρ z : ℂ} (hz_w : z ≠ w) (hz_ρ : z ≠ ρ) :
    ContinuousAt (herglotzLogIntegrand w ρ) z := by
      refine' ContinuousAt.mul _ _;
      · refine' Complex.continuous_re.continuousAt.comp _;
        refine' ContinuousAt.div _ _ _ <;> norm_num [ hz_w, hz_ρ ];
        · exact continuousAt_id.add continuousAt_const;
        · exact continuousAt_id.sub continuousAt_const;
        · exact sub_ne_zero_of_ne hz_w;
      · exact ContinuousAt.log ( ContinuousAt.norm ( continuousAt_id.sub continuousAt_const ) ) ( norm_ne_zero_iff.mpr ( sub_ne_zero.mpr hz_ρ ) )

/-
PROBLEM For `‖w‖ < r` and `0 < r < R = ‖ρ‖`, the function `θ ↦
herglotzLogIntegrand w ρ (circleMap 0 r θ)` is continuous.

PROVIDED SOLUTION

The composition of herglotzLogIntegrand w ρ with circleMap 0 r is continuous
because herglotzLogIntegrand is continuous at every point z on the circle |z| =
r (since z ≠ w because ‖w‖ < r implies ‖w‖ ≠ |r| so circleMap_zero_ne_of_norm_ne
applies, and z ≠ ρ because ‖ρ‖ = R > r implies ‖ρ‖ ≠ |r| so
circleMap_zero_ne_of_norm_ne applies), and circleMap is continuous. Use
herglotzLogIntegrand_continuousAt and continuous_circleMap.
-/
lemma herglotzLogIntegrand_continuous_on_circle
    {w ρ : ℂ} {R r : ℝ} (hR : 0 < R) (hρ : ‖ρ‖ = R)
    (hr_pos : 0 < r) (hr_lt : r < R) (hwr : ‖w‖ < r) :
    Continuous (fun θ => herglotzLogIntegrand w ρ (circleMap 0 r θ)) := by
      refine' continuous_iff_continuousAt.mpr _;
      intro θ; apply_rules [ ContinuousAt.mul, ContinuousAt.comp, continuousAt_const, continuousAt_id, continuousAt_of_tendsto_nhds ] ;
      any_goals apply_rules [ Complex.continuous_re.continuousAt, continuousAt_id ];
      · refine' ContinuousAt.div _ _ _ <;> norm_num [ circleMap ];
        · fun_prop (disch := solve_by_elim);
        · exact Continuous.continuousAt ( by continuity );
        · exact sub_ne_zero_of_ne <| ne_of_apply_ne Complex.normSq <| by norm_num [ Complex.normSq_eq_norm_sq, Complex.norm_exp ] ; nlinarith [ norm_nonneg w ] ;
      · refine' ContinuousAt.log _ _ <;> norm_num [ circleMap ];
        · exact Continuous.continuousAt ( by continuity );
        · exact sub_ne_zero_of_ne <| ne_of_apply_ne Norm.norm <| by norm_num [ Complex.norm_exp, abs_of_pos hr_pos ] ; linarith;

/-
PROBLEM
For `r ≤ R`, `‖circleMap 0 r θ - ρ‖ ≤ r + R ≤ 2 * R`.

PROVIDED SOLUTION
By triangle inequality, ‖circleMap 0 r θ - ρ‖ ≤ ‖circleMap 0 r θ‖ + ‖ρ‖ = |r| + R ≤ R + R = 2R since r ≤ R implies |r| ≤ R (using hr : 0 ≤ r).
-/
lemma norm_circleMap_sub_le {r R : ℝ} {ρ : ℂ} (hρ : ‖ρ‖ = R) (hr : 0 ≤ r) (hrR : r ≤ R) (θ : ℝ) :
    ‖circleMap 0 r θ - ρ‖ ≤ 2 * R := by
      refine' le_trans ( norm_sub_le _ _ ) _;
      simp_all +decide [ circleMap ] ; linarith [ abs_of_nonneg hr ] ;

/-!
## Additional helper lemmas for the domination bound
-/

/-
PROBLEM
Key lower bound: for `r₀ ≤ r ≤ R` and `‖ρ‖ = R`, we have
`‖circleMap 0 r θ - ρ‖² ≥ (r₀ / R) * ‖circleMap 0 R θ - ρ‖²`.

This follows from the cosine law:
  `‖circleMap 0 r θ - ρ‖² = r² + R² - 2rR cos(θ - α) ≥ 2rR(1 - cos(θ-α))`
  `≥ 2r₀R(1 - cos(θ-α)) = (r₀/R) · 2R²(1 - cos(θ-α)) = (r₀/R) · ‖circleMap 0 R θ - ρ‖²`.

PROVIDED SOLUTION
Write ρ = ‖ρ‖ * exp(I*α) for some α. Then circleMap 0 s θ = s * exp(I*θ).
‖circleMap 0 s θ - ρ‖² = s² + R² - 2sR cos(θ - α) (by the cosine law / direct computation of norm squared of the difference of two complex exponentials).
For s = r: ‖circleMap 0 r θ - ρ‖² = r² + R² - 2rR cos(θ-α) ≥ 2rR(1 - cos(θ-α)) since r² + R² ≥ 2rR.
For s = R: ‖circleMap 0 R θ - ρ‖² = 2R²(1 - cos(θ-α)).
So ‖circleMap 0 r θ - ρ‖² ≥ 2rR(1-cos(θ-α)) = (r/R) · 2R²(1-cos(θ-α)) = (r/R) · ‖circleMap 0 R θ - ρ‖² ≥ (r₀/R) · ‖circleMap 0 R θ - ρ‖².

In Lean, the cleanest approach: expand everything using Complex.normSq and compute. Use `norm_num [circleMap, Complex.normSq, Complex.norm_sq]` and `nlinarith` or `ring_nf` + `nlinarith`.
Alternatively, express ‖·‖² using sq_abs and Complex.sq_abs, and compute the differences.
-/
lemma norm_sq_circleMap_sub_lower_bound
    {r₀ r R : ℝ} {ρ : ℂ} (hρ : ‖ρ‖ = R)
    (hr₀ : 0 < r₀) (hR : 0 < R) (hr₀r : r₀ ≤ r) (hrR : r ≤ R) (θ : ℝ) :
    (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ^ 2 ≤ ‖circleMap 0 r θ - ρ‖ ^ 2 := by
      -- By the cosine law, we have ‖circleMap 0 r θ - ρ‖² = r² + R² - 2rR cos(θ - α) and ‖circleMap 0 R θ - ρ‖² = R² + R² - 2R² cos(θ - α).
      have h_cos_law : ‖circleMap 0 r θ - ρ‖ ^ 2 = r ^ 2 + R ^ 2 - 2 * r * R * Real.cos (θ - Complex.arg ρ) ∧ ‖circleMap 0 R θ - ρ‖ ^ 2 = R ^ 2 + R ^ 2 - 2 * R ^ 2 * Real.cos (θ - Complex.arg ρ) := by
        norm_num [ Complex.normSq, Complex.sq_norm, circleMap ];
        rw [ ← Complex.norm_mul_cos_arg ρ, ← Complex.norm_mul_sin_arg ρ ] ; ring_nf ; norm_num [ Real.sin_sub, Real.cos_sub, hρ ];
        constructor <;> rw [ Real.sin_sq, Real.sin_sq ] <;> ring;
      rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith [ mul_le_mul_of_nonneg_left hr₀r hR.le, mul_le_mul_of_nonneg_left hrR hR.le, Real.neg_one_le_cos ( θ - ρ.arg ), Real.cos_le_one ( θ - ρ.arg ) ]

/-
PROBLEM
Consequence: `‖circleMap 0 r θ - ρ‖ ≥ √(r₀/R) * ‖circleMap 0 R θ - ρ‖`.

PROVIDED SOLUTION
From norm_sq_circleMap_sub_lower_bound we have (r₀/R) * ‖circleMap 0 R θ - ρ‖² ≤ ‖circleMap 0 r θ - ρ‖². Taking square roots of both sides (both sides are nonneg), we get √(r₀/R) * ‖circleMap 0 R θ - ρ‖ ≤ ‖circleMap 0 r θ - ρ‖. Use Real.sqrt_le_sqrt and Real.sqrt_mul_self or nonneg_of_mul_nonneg_left, and Real.sqrt_mul to split √(a*b) = √a * √b.
-/
lemma norm_circleMap_sub_lower_bound
    {r₀ r R : ℝ} {ρ : ℂ} (hρ : ‖ρ‖ = R)
    (hr₀ : 0 < r₀) (hR : 0 < R) (hr₀r : r₀ ≤ r) (hrR : r ≤ R) (θ : ℝ) :
    Real.sqrt (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ≤ ‖circleMap 0 r θ - ρ‖ := by
      convert Real.sqrt_le_sqrt ( norm_sq_circleMap_sub_lower_bound hρ hr₀ hR hr₀r hrR θ ) using 1 ; ring_nf ; norm_num [ hr₀.le, hR.le ] ; ring_nf ; aesop;

/-
PROBLEM
For `z` on the circle of radius `r` with `‖w‖ < r`, the Herglotz–Riesz kernel is bounded:
`|Re((z + w)/(z - w))| ≤ (r + ‖w‖) / (r - ‖w‖)`.

PROVIDED SOLUTION
We have (Complex.re ∘ herglotzRieszKernel 0 w) z = Re((z + w) / (z - w)).
|Re((z+w)/(z-w))| ≤ |(z+w)/(z-w)| = ‖z+w‖/‖z-w‖ ≤ (‖z‖ + ‖w‖)/(‖z‖ - ‖w‖) = (r + ‖w‖)/(r - ‖w‖).
The last inequality uses ‖z-w‖ ≥ ‖z‖ - ‖w‖ = r - ‖w‖ > 0 and ‖z+w‖ ≤ ‖z‖ + ‖w‖.
The norm of the real part ‖Re(·)‖ = |Re(·)| ≤ ‖·‖ by Complex.abs_re_le_abs or similar.
Use norm_div, norm_add_le, and div_le_div_of_nonneg for the fraction bound.
-/
lemma herglotzRieszKernel_re_bound
    {w z : ℂ} {r : ℝ} (hr : 0 < r) (hw : ‖w‖ < r) (hz : ‖z‖ = r) :
    ‖(Complex.re ∘ herglotzRieszKernel 0 w) z‖ ≤ (r + ‖w‖) / (r - ‖w‖) := by
      -- By the properties of the Herglotz-Riesz kernel and the triangle inequality, we have:
      have h_bound : ‖(z + w) / (z - w)‖ ≤ (r + ‖w‖) / (r - ‖w‖) := by
        rw [ norm_div ];
        gcongr;
        · linarith;
        · exact le_trans ( norm_add_le _ _ ) ( by linarith );
        · simpa [ hz ] using norm_sub_norm_le z w;
      unfold herglotzRieszKernel;
      simpa using le_trans ( Complex.abs_re_le_norm _ ) h_bound

/-
PROBLEM
The Poisson kernel `(s + a)/(s - a)` is decreasing in `s` for `s > a > 0`.

PROVIDED SOLUTION
We want (s₂+a)/(s₂-a) ≤ (s₁+a)/(s₁-a). Cross-multiply (both denominators are positive since s₂ ≥ s₁ > a): (s₂+a)(s₁-a) ≤ (s₁+a)(s₂-a). Expand: s₁s₂ - as₂ + as₁ - a² ≤ s₁s₂ - as₁ + as₂ - a². This simplifies to 2a(s₁ - s₂) ≤ 0, which is true since a ≥ 0 and s₁ ≤ s₂. Use div_le_div_iff and nlinarith.
-/
lemma poisson_kernel_antitone {a s₁ s₂ : ℝ} (ha : 0 ≤ a) (hs₁ : a < s₁) (hs₂ : s₁ ≤ s₂) :
    (s₂ + a) / (s₂ - a) ≤ (s₁ + a) / (s₁ - a) := by
      rw [ div_le_div_iff₀ ] <;> nlinarith

/-
PROBLEM
Bound on `|log ‖z - ρ‖|` for `z` on a circle of radius `r` with `r₀ ≤ r ≤ R`,
where `‖ρ‖ = R`, and `circleMap 0 R θ ≠ ρ` (so `‖circleMap 0 R θ - ρ‖ > 0`).

PROVIDED SOLUTION
Set d := ‖circleMap 0 r θ - ρ‖ and dR := ‖circleMap 0 R θ - ρ‖ and c := Real.sqrt (r₀ / R).

Key facts:
- d ≤ 2 * R (by norm_circleMap_sub_le hρ (by linarith) hrR θ)
- c * dR ≤ d (by norm_circleMap_sub_lower_bound hρ hr₀ hR hr₀r hrR θ)
- c > 0 (since r₀/R > 0, sqrt positive)
- dR > 0 (hypothesis hdR)
- d > 0 (since d ≥ c * dR > 0)

We prove |log d| ≤ |log(2*R)| + |log c| + |log dR| by showing both directions:

Upper bound (log d ≤ RHS):
  log d ≤ log(2*R) (since 0 < d ≤ 2*R, use Real.log_le_log)
  log(2*R) ≤ |log(2*R)| (le_abs_self)
  |log(2*R)| ≤ RHS (add nonneg terms)

Lower bound (-RHS ≤ log d):
  log d ≥ log(c * dR) (since d ≥ c*dR > 0, use Real.log_le_log)
  log(c * dR) = log c + log dR (Real.log_mul, c > 0, dR > 0)
  log c + log dR ≥ -|log c| + (-|log dR|) = -|log c| - |log dR| (neg_abs_le)
  -|log c| - |log dR| ≥ -|log(2*R)| - |log c| - |log dR| (subtract nonneg |log(2*R)|)

Combine with abs_le.mpr.
-/
lemma abs_log_norm_circleMap_sub_bound
    {ρ : ℂ} {R r₀ r : ℝ} (hR : 0 < R) (hρ : ‖ρ‖ = R)
    (hr₀ : 0 < r₀) (hr₀r : r₀ ≤ r) (hrR : r ≤ R) (θ : ℝ)
    (hdR : 0 < ‖circleMap 0 R θ - ρ‖) :
    |Real.log ‖circleMap 0 r θ - ρ‖| ≤
      |Real.log (2 * R)| + |Real.log (Real.sqrt (r₀ / R))| +
      |Real.log ‖circleMap 0 R θ - ρ‖| := by
        refine' abs_le.mpr ⟨ _, _ ⟩;
        · -- By the properties of logarithms and absolute values, we can show that Real.log ‖circleMap 0 r θ - ρ‖ is bounded below by Real.log (√(r₀/R)) + Real.log ‖circleMap 0 R θ - ρ‖.
          have h_log_lower_bound : Real.log ‖circleMap 0 r θ - ρ‖ ≥ Real.log (Real.sqrt (r₀ / R)) + Real.log ‖circleMap 0 R θ - ρ‖ := by
            rw [ ← Real.log_mul ( by positivity ) ( by positivity ) ];
            exact Real.log_le_log ( mul_pos ( Real.sqrt_pos.mpr ( div_pos hr₀ hR ) ) hdR ) ( by linarith [ norm_circleMap_sub_lower_bound hρ hr₀ hR hr₀r hrR θ ] );
          grind;
        · refine' le_trans _ ( le_add_of_le_of_nonneg ( le_add_of_nonneg_right <| abs_nonneg _ ) <| abs_nonneg _ );
          refine' le_trans ( Real.log_le_log ( _ ) _ ) ( le_abs_self _ );
          · refine' lt_of_lt_of_le _ ( norm_circleMap_sub_lower_bound hρ hr₀ hR hr₀r hrR θ ) ; aesop;
          · exact norm_circleMap_sub_le hρ ( by linarith ) ( by linarith ) _

/-
PROBLEM
Bound on the full integrand on a circle of radius `r`.

PROVIDED SOLUTION
The integrand is herglotzLogIntegrand w ρ (circleMap 0 r θ) which by definition equals (Re ∘ herglotzRieszKernel 0 w)(z) * log ‖z - ρ‖ where z = circleMap 0 r θ.

So ‖herglotzLogIntegrand w ρ z‖ = |(Re ∘ herglotzRieszKernel 0 w)(z)| * |log ‖z - ρ‖|.

Step 1 (Poisson kernel bound):
By herglotzRieszKernel_re_bound with ‖z‖ = r (via norm_circleMap_zero'), ‖w‖ < r₀ ≤ r:
  ‖(Re ∘ herglotzRieszKernel 0 w)(z)‖ ≤ (r + ‖w‖)/(r - ‖w‖)
By poisson_kernel_antitone with a = ‖w‖, s₁ = r₀, s₂ = r:
  (r + ‖w‖)/(r - ‖w‖) ≤ (r₀ + ‖w‖)/(r₀ - ‖w‖)
Wait, poisson_kernel_antitone says (s₂+a)/(s₂-a) ≤ (s₁+a)/(s₁-a) when s₁ ≤ s₂.
So with s₁ = r₀, s₂ = r, a = ‖w‖: (r + ‖w‖)/(r - ‖w‖) ≤ (r₀ + ‖w‖)/(r₀ - ‖w‖).
And (r₀ + ‖w‖)/(r₀ - ‖w‖) ≤ (R + ‖w‖)/(r₀ - ‖w‖) since r₀ ≤ R.

Step 2 (log bound):
By abs_log_norm_circleMap_sub_bound:
  |log ‖z - ρ‖| ≤ log(2R) + |log √(r₀/R)| + |log ‖circleMap 0 R θ - ρ‖|.

Step 3: multiply the two bounds.
-/
lemma herglotzLogIntegrand_bound
  {w ρ : ℂ} {R r₀ r : ℝ} (hR : 0 < R) (hρ : ‖ρ‖ = R)
  (hr₀ : 0 < r₀) (hw : ‖w‖ < r₀) (hr₀r : r₀ ≤ r) (hrR : r ≤ R) (θ : ℝ)
  (hdR : 0 < ‖circleMap 0 R θ - ρ‖) :
  ‖herglotzLogIntegrand w ρ (circleMap 0 r θ)‖ ≤
    ((R + ‖w‖) / (r₀ - ‖w‖)) *
    (|Real.log (2 * R)| + |Real.log (Real.sqrt (r₀ / R))| +
     |Real.log ‖circleMap 0 R θ - ρ‖|) := by
  -- By the properties of the norm, we have:
  have h_norm : ‖(Complex.re ∘ herglotzRieszKernel 0 w) (circleMap 0 r θ)‖ ≤ (R + ‖w‖) / (r₀ - ‖w‖) := by
    have h_bound : ‖(Complex.re ∘ herglotzRieszKernel 0 w) (circleMap 0 r θ)‖ ≤ (r + ‖w‖) / (r - ‖w‖) := by
      convert herglotzRieszKernel_re_bound
        (show 0 < r by linarith)
        (show ‖w‖ < r by linarith)
        (show ‖circleMap 0 r θ‖ = r by rw [norm_circleMap_zero']; rw [abs_of_nonneg]; linarith)
        using 1;
    exact h_bound.trans (by rw [div_le_div_iff₀] <;> nlinarith [norm_nonneg w])
  have h_log : |Real.log ‖circleMap 0 r θ - ρ‖| ≤ |Real.log (2 * R)| + |Real.log (Real.sqrt (r₀ / R))| + |Real.log ‖circleMap 0 R θ - ρ‖| := by
    apply abs_log_norm_circleMap_sub_bound hR hρ hr₀ hr₀r hrR θ hdR;
  unfold herglotzLogIntegrand
  simp
  exact mul_le_mul h_norm h_log (by positivity)
    (by exact div_nonneg (by linarith [norm_nonneg w]) (by linarith [norm_nonneg w]))

/-!
## The specific convergence result
-/

/-
PROBLEM
For `‖ρ‖ = R > 0`, `‖w‖ < R`, and a monotone sequence `r n ↗ R`, the circle averages
`circleAverage (herglotzLogIntegrand w ρ) 0 (r n)` converge to
`circleAverage (herglotzLogIntegrand w ρ) 0 R`.

PROVIDED SOLUTION
Apply circleAverage_tendsto_of_tendsto_radius hr_tendsto with:
  bound := fun θ => ((R + ‖w‖) / (r 0 - ‖w‖)) * (|Real.log (2 * R)| + |Real.log (Real.sqrt (r 0 / R))| + |Real.log ‖circleMap 0 R θ - ρ‖|)

Wait, we need r 0 > ‖w‖ which may not hold. Since r n → R and ‖w‖ < R, ∃ N₀ such that for n ≥ N₀, r n > ‖w‖. Use r N₀ as r₀. But for simplicity, just use (R + ‖w‖) / 2 as r₀ since we can find n₀ with r n₀ > (R + ‖w‖) / 2.

Actually, since hr_mono (monotone) and hr_tendsto: r n → R and ‖w‖ < R, eventually ‖w‖ < r n. Let N₀ be such that r N₀ > ‖w‖. Set r₀ := r N₀. Then for all n ≥ N₀, r₀ ≤ r n ≤ R and ‖w‖ < r₀.

Bound function: bound θ := C * (|log(2R)| + |log(√(r₀/R))| + |log ‖circleMap 0 R θ - ρ‖|) where C = (R + ‖w‖)/(r₀ - ‖w‖).

1. **Integrability of bound**: bound is integrable since |log ‖circleMap 0 R θ - ρ‖| is integrable (from intervalIntegrable_log_norm_circleMap_sub with .abs) and constant functions are integrable. Use IntervalIntegrable.const_mul and IntervalIntegrable.add.

2. **Measurability**: For each n (≥ N₀), θ ↦ herglotzLogIntegrand w ρ (circleMap 0 (r n) θ) is continuous by herglotzLogIntegrand_continuous_on_circle (since ‖w‖ < r₀ ≤ r n and r n < R), hence AEStronglyMeasurable.

3. **Domination**: For n ≥ N₀ and a.e. θ (specifically θ with ‖circleMap 0 R θ - ρ‖ > 0), by herglotzLogIntegrand_bound: ‖integrand‖ ≤ bound θ. The set {θ : ‖circleMap 0 R θ - ρ‖ = 0} has measure zero (at most one point in [0, 2π]).

4. **Pointwise convergence**: For a.e. θ (those with circleMap 0 R θ ≠ w and circleMap 0 R θ ≠ ρ), herglotzLogIntegrand w ρ (circleMap 0 (r n) θ) → herglotzLogIntegrand w ρ (circleMap 0 R θ) by herglotzLogIntegrand_continuousAt (since circleMap 0 R θ ≠ w and ≠ ρ) composed with circleMap 0 (r n) θ → circleMap 0 R θ (by continuity of circleMap in radius, using hr_tendsto).

For the a.e. conditions: {θ : circleMap 0 R θ = w} is empty (since ‖w‖ < R = ‖circleMap 0 R θ‖). {θ : circleMap 0 R θ = ρ} has at most 1 point (measure 0).

The key Lean tactics:
- Use Filter.Eventually.of_forall or eventually_atTop for the "eventually" conditions
- Use Filter.Eventually.mono for the ae conditions
- For pointwise convergence of circleMap in radius: circleMap 0 (r n) θ = (r n) * exp(I * θ) and r n → R, so this converges to R * exp(I * θ) = circleMap 0 R θ. Use Filter.Tendsto.const_mul or similar.
-/
private theorem herglotzLogIntegrand_circleAverage_tendsto
    {ρ w : ℂ} {R : ℝ} (hR : 0 < R) (hρ : ‖ρ‖ = R) (hw : ‖w‖ < R)
    {r : ℕ → ℝ} (hr_lt : ∀ n, r n < R) (hr_pos : ∀ n, 0 < r n)
    (hr_tendsto : Tendsto r atTop (nhds R)) :
    Tendsto (fun n ↦ circleAverage (herglotzLogIntegrand w ρ) 0 (r n)) atTop
      (nhds (circleAverage (herglotzLogIntegrand w ρ) 0 R)) := by
  -- Apply the dominated convergence theorem.
  let bound := fun θ ↦ ((R + ‖w‖) / ((R + ‖w‖) / 2 - ‖w‖)) * (|Real.log (2 * R)| + |Real.log (Real.sqrt ((R + ‖w‖) / 2 / R))| + |Real.log ‖circleMap 0 R θ - ρ‖|)
  apply circleAverage_tendsto_of_tendsto_radius (bound := bound)
  · -- IntervalIntegrable bound volume 0 (2 * π)
    apply IntervalIntegrable.const_mul
    apply IntervalIntegrable.add
    · exact IntervalIntegrable.add (by simp) (by continuity)
    · apply IntervalIntegrable.abs
      exact circleIntegrable_log_norm_meromorphicOn (f := fun z ↦ z - ρ)
        (fun x hx ↦ by fun_prop)
  · -- The herglotzLogIntegrand is AEStronglyMeasurable
    filter_upwards [hr_tendsto.eventually (lt_mem_nhds hw) ] with n hn
    apply Continuous.aestronglyMeasurable
    apply_rules [herglotzLogIntegrand_continuous_on_circle]
  · -- Pointwise boundedness outside a null set
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, r n > (R + ‖w‖) / 2 :=
      Filter.eventually_atTop.mp (hr_tendsto.eventually (lt_mem_nhds (by linarith)))
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have h_bound {θ : ℝ} : ‖herglotzLogIntegrand w ρ (circleMap 0 (r n) θ)‖ ≤ bound θ ∨ ‖circleMap 0 R θ - ρ‖ = 0 := by
      unfold bound
      by_cases h : ‖circleMap 0 R θ - ρ‖ = 0
      <;> simp_all [circleMap]
      convert herglotzLogIntegrand_bound hR hρ
        (show 0 < (R + ‖w‖) / 2 by linarith [norm_nonneg w])
        (show ‖w‖ < (R + ‖w‖) / 2 by linarith [norm_nonneg w])
        (show (R + ‖w‖) / 2 ≤ r n by linarith [hN n hn])
        (show r n ≤ R by linarith [hr_lt n]) θ _
        using 1
      · norm_num [circleMap]
      · norm_num [circleMap]
      · exact norm_pos_iff.mpr (by simpa [circleMap] using h)
    apply MeasureTheory.measure_mono_null (t := {θ | ‖circleMap 0 R θ - ρ‖ = 0}) (by grind)
    apply Set.Countable.measure_zero _ MeasureTheory.MeasureSpace.volume
    simp only [norm_eq_zero, sub_eq_zero]
    exact (countable_singleton ρ).preimage_circleMap 0 (hR.ne')
  · -- Pointwise convergence outside a null set
    have h_measure_zero : MeasureTheory.volume {θ : ℝ | circleMap 0 R θ = w ∨ circleMap 0 R θ = ρ} = 0 := by
      apply Set.Countable.measure_zero _ MeasureTheory.MeasureSpace.volume
      exact Set.Countable.union ((countable_singleton w).preimage_circleMap 0 (hR.ne'))
          ((countable_singleton ρ).preimage_circleMap 0 (hR.ne'))
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_measure_zero] with θ hθ
    intro _
    apply (herglotzLogIntegrand_continuousAt (by tauto) (by tauto)).tendsto.comp
    apply Filter.Tendsto.add tendsto_const_nhds
      (Filter.Tendsto.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hr_tendsto)
        tendsto_const_nhds)

theorem xx (w ρ : ℂ)
    {R : ℝ} (hR : 0 < R) (hρ : ‖ρ‖ = R) (hw : ‖w‖ < R)  :
    circleAverage (herglotzLogIntegrand w ρ) (0 : ℂ) R = Real.log ‖w - ρ‖ := by
  let r : ℕ → ℝ := fun n ↦ R - (R - ‖w‖) / (n + 2)
  have hr_lt : ∀ n, r n < R := by
    intro n
    simp_all only [sub_lt_self_iff, sub_pos, div_pos_iff_of_pos_left, r]
    linarith
  have hr_pos : ∀ n, 0 < r n := by
    intro n
    simp_all only [sub_lt_self_iff, sub_pos, div_pos_iff_of_pos_left, r]
    apply (div_lt_iff₀ (by linarith)).2
    calc R - ‖w‖
      _ ≤ R := by aesop
      _ < R * (n + 2) := by
        rw [lt_mul_iff_one_lt_right hR]
        linarith
  have hr_tendsto : Tendsto r atTop (nhds R) :=
    le_trans (tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <|
      Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      (by norm_num)
  have DCT := herglotzLogIntegrand_circleAverage_tendsto hR hρ hw hr_lt hr_pos hr_tendsto
  have {n : ℕ} : circleAverage (herglotzLogIntegrand w ρ) 0 (r n) = Real.log ‖w - ρ‖ := by
    unfold herglotzLogIntegrand
    rw [InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul]
    · constructor
      · intro z hz
        have : z ≠ ρ := by
          by_contra h
          simp only [mem_ball, dist_zero_right] at hz
          grind
        apply AnalyticAt.harmonicAt_log_norm (by fun_prop) (by grind)
      · intro x hx
        apply ContinuousAt.continuousWithinAt
        have : ‖x - ρ‖ ≠ 0 := by
          by_contra h
          rw [norm_eq_zero, sub_eq_zero] at h
          rw [closure_ball _ (by grind), mem_closedBall, dist_zero_right] at hx
          grind
        fun_prop (disch := grind)
    · simp [r, lt_sub_iff_add_lt]
      apply add_lt_of_lt_neg_add
      nth_rw 2 [add_comm]
      rw [← sub_eq_add_neg]
      exact div_lt_self (by simp_all) (by linarith)
  aesop
