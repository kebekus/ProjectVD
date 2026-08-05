/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import VD.MathlibSubmitted.MeromorphicLogDeriv
import VD.LLD.PoissonSchwarzDeriv

/-!
# The Differentiated Poisson–Jensen Formula — LLD work package B6

See `VD/LLD/PLAN-LogarithmicDerivative.md`, §4.

Mathlib target: new file `Mathlib/Analysis/Complex/PoissonJensenDeriv.lean`.
Dependencies: `VD/LLD/MeromorphicLogDeriv.lean` (work package A) and
`VD/LLD/PoissonSchwarzDeriv.lean` (work packages B4–B5).

This file establishes the **differentiated Poisson–Jensen formula**
`MeromorphicOn.logDeriv_eqOn_codiscrete`: for `f` meromorphic on `closedBall 0 R` with
meromorphic order `≠ ⊤` everywhere, the logarithmic derivative of `f` agrees, away from a
discrete subset of the open ball, with

- the circle average of `log ‖f ·‖` against the `w`-derivative `2ζ/(ζ-w)²` of the
  Herglotz–Riesz kernel, minus
- the sum of the logarithmic derivatives of the canonical factors, weighted by the divisor
  of `f` on the ball.

Sign check (`f = id`, `R = 1`): `divisor = δ₀`, `canonicalFactor 1 0 = (·)⁻¹`,
`logDeriv (·)⁻¹ w = -1/w`, kernel term `= 0`; RHS `= 0 - (-1/w) = 1/w = logDeriv id w`. ✓

The proof mirrors that of the Poisson–Jensen formula in `VD/MathlibPending/PoissonJensen.lean`:
take the extended canonical decomposition (`exists_ecanonicalDecomp`), apply the codiscrete
`logDeriv` arithmetic from work package A, and rewrite `logDeriv h` of the nonvanishing factor
via the differentiated Poisson representation (B4). On the sphere the canonical-factor terms
vanish (`norm_canonicalFactor_eval_circle_eq_one`), and each boundary-divisor term integrates
to `(w - v)⁻¹` (`circleAverage_smul_log_norm_sub_sphere`), cancelling exactly against the
logarithmic derivatives of the boundary factors.
-/

open Complex Filter Function MeromorphicOn Metric Real Set Topology

/-!
## Auxiliary Lemmas
-/

@[fun_prop]
lemma meromorphicAt_canonicalFactor {R : ℝ} {x w : ℂ} : MeromorphicAt (canonicalFactor R w) x := by
  rw [canonicalFactor_def]
  fun_prop

/-- The derived Herglotz–Riesz kernel `ζ ↦ 2ζ/(ζ-w)²` is continuous on the circle
`sphere 0 |R|` whenever `w ∈ ball 0 R`. -/
private lemma continuousOn_derivedKernel {w : ℂ} {R : ℝ} (hw : w ∈ ball 0 R) :
    ContinuousOn (fun ζ : ℂ ↦ 2 * ζ / (ζ - w) ^ 2) (sphere (0 : ℂ) |R|) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro z hz
  apply pow_ne_zero
  rw [sub_ne_zero]
  grind [mem_sphere, mem_ball, le_abs_self R]

/-- If `g` is meromorphic on the closed ball and `w` lies in the open ball, then
`ζ ↦ (2ζ/(ζ-w)²) • log ‖g ζ‖` is circle integrable. -/
private lemma circleIntegrable_derivedKernel_smul_log_norm {g : ℂ → ℂ} {w : ℂ} {R : ℝ}
    (hg : MeromorphicOn g (closedBall 0 R)) (hw : w ∈ ball 0 R) :
    CircleIntegrable (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖g ζ‖ : ℂ)) 0 R := by
  have hR : 0 < R := pos_of_mem_ball hw
  have h₁ : CircleIntegrable (fun ζ ↦ Real.log ‖g ζ‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm
      (hg.mono_set (by rw [abs_of_pos hR]; exact sphere_subset_closedBall))
  have h₂ : CircleIntegrable (fun ζ ↦ (Real.log ‖g ζ‖ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at h₁ ⊢
    exact Complex.ofRealCLM.integrable_comp h₁
  exact h₂.smul_of_continuousOn (continuousOn_derivedKernel hw)

/-- The meromorphic order of `· - v` is never `⊤`. -/
private lemma meromorphicOrderAt_id_sub_const_ne_top {v x : ℂ} :
    meromorphicOrderAt (· - v) x ≠ ⊤ := by
  have hm : MeromorphicAt (fun z : ℂ ↦ z - v) x :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero hm]
  rcases eq_or_ne x v with rfl | hxv
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact sub_ne_zero.2 hz
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds hxv)] with z hz
    exact sub_ne_zero.2 hz

/-- The logarithmic derivative of `· - v`. -/
private lemma logDeriv_id_sub_const (v w : ℂ) : logDeriv (· - v) w = (w - v)⁻¹ := by
  have h : HasDerivAt (fun z : ℂ ↦ z - v) 1 w := by simpa using (hasDerivAt_id w).sub_const v
  rw [logDeriv_apply, h.deriv, one_div]

/-!
## The Differentiated Poisson–Jensen Formula
-/

/-- **Differentiated Poisson–Jensen formula**: away from a discrete set, the logarithmic
derivative of a meromorphic function on `closedBall 0 R` is the circle average of `log ‖f ·‖`
against the `w`-derivative of the Herglotz–Riesz kernel, corrected by the logarithmic
derivatives of the canonical factors. -/
theorem MeromorphicOn.logDeriv_eqOn_codiscrete {f : ℂ → ℂ} {R : ℝ}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : closedBall (0 : ℂ) R, meromorphicOrderAt f u ≠ ⊤) :
    logDeriv f =ᶠ[codiscreteWithin (ball 0 R)]
      fun w ↦ circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖f ζ‖ : ℂ)) 0 R
        - ∑ᶠ a, (divisor f (ball 0 R) a) • logDeriv (canonicalFactor R a) w := by
  -- The statement is vacuous for `R ≤ 0`, where the ball is empty.
  by_cases hR : 0 < R
  case neg =>
    filter_upwards [self_mem_codiscreteWithin (ball 0 R)] with a ha
    simp [ball_eq_empty.2 (not_lt.1 hR)] at ha
  -- Write `f = (Blaschke product) • h` with `h` analytic and nowhere zero on the closed
  -- ball, where the Blaschke product collects the zeros and poles of `f`.
  obtain ⟨h, D⟩ := h₁f.exists_ecanonicalDecomp h₂f
  have h₃f : (divisor f (sphere 0 R)).support.Finite := divisor_sphere_support_finite
  have h₄f : (divisor f (ball 0 R)).support.Finite := h₁f.divisor_ball_support_finite
  -- Meromorphy of the three factors of the decomposition on the ball
  have hBmero : MeromorphicOn
      (∏ᶠ u, canonicalFactor R u ^ (-divisor f (ball 0 R) u)) (ball 0 R) :=
    fun x _ ↦ MeromorphicAt.finprod fun u ↦ meromorphicAt_canonicalFactor.zpow _
  have hSmero : MeromorphicOn
      (∏ᶠ v, (· - v) ^ divisor f (sphere 0 R) v) (ball 0 R) :=
    fun x _ ↦ MeromorphicAt.finprod fun v ↦
      ((analyticAt_id.sub analyticAt_const).meromorphicAt).zpow _
  have hhmero : MeromorphicOn h (ball 0 R) :=
    fun x hx ↦ (D.analyticOnNhd x (ball_subset_closedBall hx)).meromorphicAt
  -- The meromorphic orders of the three factors are nowhere `⊤` on the ball
  have hBord : ∀ x ∈ ball (0 : ℂ) R,
      meromorphicOrderAt (∏ᶠ u, canonicalFactor R u ^ (-divisor f (ball 0 R) u)) x ≠ ⊤ := by
    intro x hx
    rw [finprod_eq_prod_of_mulSupport_subset (s := h₄f.toFinset) _ (by aesop),
      meromorphicOrderAt_prod (fun u _ ↦ meromorphicAt_canonicalFactor.zpow _),
      WithTop.sum_ne_top]
    intro u _
    rw [meromorphicOrderAt_zpow meromorphicAt_canonicalFactor]
    exact WithTop.mul_ne_top WithTop.coe_ne_top (meromorphicOrderAt_canonicalFactor_ne_top u hR)
  have hSord : ∀ x ∈ ball (0 : ℂ) R,
      meromorphicOrderAt (∏ᶠ v, (· - v) ^ divisor f (sphere 0 R) v) x ≠ ⊤ := by
    intro x hx
    rw [finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _ (by aesop),
      meromorphicOrderAt_prod
        (fun v _ ↦ ((analyticAt_id.sub analyticAt_const).meromorphicAt).zpow _),
      WithTop.sum_ne_top]
    intro v _
    rw [meromorphicOrderAt_zpow ((analyticAt_id.sub analyticAt_const).meromorphicAt)]
    exact WithTop.mul_ne_top WithTop.coe_ne_top meromorphicOrderAt_id_sub_const_ne_top
  have hhord : ∀ x ∈ ball (0 : ℂ) R, meromorphicOrderAt h x ≠ ⊤ := by
    intro x hx
    have ha := D.analyticOnNhd x (ball_subset_closedBall hx)
    have h₀ : meromorphicOrderAt h x = 0 := by
      rw [ha.meromorphicOrderAt_eq,
        ha.analyticOrderAt_eq_zero.2 (D.ne_zero x (ball_subset_closedBall hx))]
      rfl
    simp [h₀]
  -- Step 1: Replace `f` by its canonical decomposition.
  have e₀ : logDeriv f =ᶠ[codiscreteWithin (ball 0 R)]
      logDeriv ((∏ᶠ u, canonicalFactor R u ^ (-divisor f (ball 0 R) u))
        * (∏ᶠ v, (· - v) ^ divisor f (sphere 0 R) v) * h) := by
    apply logDeriv_congr_codiscreteWithin isOpen_ball
    filter_upwards [D.eventuallyEq.filter_mono (codiscreteWithin_mono ball_subset_closedBall)]
      with z hz
    simp only [Pi.smul_apply', Pi.mul_apply, smul_eq_mul] at hz ⊢
    exact hz
  -- Step 2: The logarithmic derivative converts the product into a sum.
  have e₁ : logDeriv ((∏ᶠ u, canonicalFactor R u ^ (-divisor f (ball 0 R) u))
        * (∏ᶠ v, (· - v) ^ divisor f (sphere 0 R) v) * h)
      =ᶠ[codiscreteWithin (ball 0 R)]
      logDeriv (∏ᶠ u, canonicalFactor R u ^ (-divisor f (ball 0 R) u))
        + logDeriv (∏ᶠ v, (· - v) ^ divisor f (sphere 0 R) v) + logDeriv h := by
    have hBSmero : MeromorphicOn ((∏ᶠ u, canonicalFactor R u ^ (-divisor f (ball 0 R) u))
        * (∏ᶠ v, (· - v) ^ divisor f (sphere 0 R) v)) (ball 0 R) :=
      fun x hx ↦ (hBmero x hx).mul (hSmero x hx)
    have hBSord : ∀ x ∈ ball (0 : ℂ) R,
        meromorphicOrderAt ((∏ᶠ u, canonicalFactor R u ^ (-divisor f (ball 0 R) u))
          * (∏ᶠ v, (· - v) ^ divisor f (sphere 0 R) v)) x ≠ ⊤ := by
      intro x hx
      rw [meromorphicOrderAt_mul (hBmero x hx) (hSmero x hx)]
      exact WithTop.add_ne_top.2 ⟨hBord x hx, hSord x hx⟩
    exact (hBSmero.logDeriv_mul_eventuallyEq hhmero hBSord hhord).trans
      ((hBmero.logDeriv_mul_eventuallyEq hSmero hBord hSord).add EventuallyEq.rfl)
  -- Step 3: Expand the logarithmic derivatives of the two products.
  have e₂ : logDeriv (∏ᶠ u, canonicalFactor R u ^ (-divisor f (ball 0 R) u))
      =ᶠ[codiscreteWithin (ball 0 R)]
      fun z ↦ ∑ᶠ u, (-divisor f (ball 0 R) u) • logDeriv (canonicalFactor R u) z := by
    apply logDeriv_finprod_zpow_eventuallyEq
      (h₄f.subset fun u hu ↦ mem_support.2 (neg_ne_zero.1 (mem_support.1 hu)))
      (fun u x _ ↦ meromorphicAt_canonicalFactor)
      (fun u x _ ↦ meromorphicOrderAt_canonicalFactor_ne_top u hR)
  have e₃ : logDeriv (∏ᶠ v, (· - v) ^ divisor f (sphere 0 R) v)
      =ᶠ[codiscreteWithin (ball 0 R)]
      fun z ↦ ∑ᶠ v, (divisor f (sphere 0 R) v) • logDeriv (· - v) z := by
    apply logDeriv_finprod_zpow_eventuallyEq h₃f
      (fun v x _ ↦ (analyticAt_id.sub analyticAt_const).meromorphicAt)
      (fun v x _ ↦ meromorphicOrderAt_id_sub_const_ne_top)
  -- Step 4, the analytic core: rewrite the circle average of `log ‖f ·‖` against the derived
  -- kernel in terms of the boundary divisor and `logDeriv h`, using the differentiated Poisson
  -- representation (B4). On the sphere, the canonical factors have norm one and drop out; each
  -- boundary factor integrates to `(w - v)⁻¹`.
  have key : ∀ w ∈ ball (0 : ℂ) R,
      circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖f ζ‖ : ℂ)) 0 R
        = (∑ v ∈ h₃f.toFinset, (divisor f (sphere 0 R) v) • (w - v)⁻¹) + logDeriv h w := by
    intro w hw
    -- Integrability of the individual summands
    have ιh : CircleIntegrable (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖h ζ‖ : ℂ)) 0 R :=
      circleIntegrable_derivedKernel_smul_log_norm
        (fun x hx ↦ (D.analyticOnNhd x hx).meromorphicAt) hw
    have ιv : ∀ v ∈ h₃f.toFinset, CircleIntegrable (fun ζ ↦ (divisor f (sphere 0 R) v : ℂ) •
        ((2 * ζ / (ζ - w) ^ 2) • (Real.log ‖ζ - v‖ : ℂ))) 0 R :=
      fun v _ ↦ (circleIntegrable_derivedKernel_smul_log_norm
        (fun x _ ↦ (analyticAt_id.sub analyticAt_const).meromorphicAt) hw).const_fun_smul
    -- Nonvanishing of the boundary factors away from the boundary divisor
    have hprodne {a : ℂ} (ha : divisor f (sphere 0 R) a = 0) :
        ∀ b ∈ h₃f.toFinset, ‖a - b‖ ^ (divisor f (sphere 0 R)) b ≠ 0 := by
      intro b hb
      refine zpow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 ?_))
      rintro rfl
      exact (h₃f.mem_toFinset.1 hb) ha
    calc circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖f ζ‖ : ℂ)) 0 R
      -- Replace `f` by its canonical decomposition
      _ = circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) •
            (Real.log ‖(((∏ᶠ u, canonicalFactor R u ^ (-divisor f (ball 0 R) u))
              * (∏ᶠ v, (· - v) ^ divisor f (sphere 0 R) v)) • h) ζ‖ : ℂ)) 0 R := by
          apply circleAverage_congr_codiscreteWithin _ hR.ne'
          rw [abs_of_pos hR]
          filter_upwards [D.eventuallyEq.filter_mono
            (codiscreteWithin_mono sphere_subset_closedBall)] with a ha
          simp only [ha]
      -- The canonical factors have norm one on the sphere
      _ = circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) •
            (Real.log ‖((∏ᶠ v, (· - v) ^ divisor f (sphere 0 R) v) • h) ζ‖ : ℂ)) 0 R := by
          apply circleAverage_congr_sphere
          intro a ha
          rw [abs_of_pos hR] at ha
          have hBa : ‖(∏ᶠ u, canonicalFactor R u ^ (-divisor f (ball 0 R) u)) a‖ = 1 := by
            rw [finprod_eq_prod_of_mulSupport_subset (s := h₄f.toFinset) _ (by aesop)]
            simp only [Finset.prod_apply, Pi.pow_apply, norm_prod, norm_zpow]
            apply Finset.prod_eq_one
            intro b hb
            rw [norm_canonicalFactor_eval_circle_eq_one
              ((divisor f (ball 0 R)).supportWithinDomain (h₄f.mem_toFinset.1 hb)) ha, one_zpow]
          simp only [Pi.smul_apply', Pi.mul_apply, norm_smul, norm_mul, hBa, one_mul]
      -- Expand the logarithm of the remaining product
      _ = circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) •
            ((∑ v ∈ h₃f.toFinset, (divisor f (sphere 0 R) v) * Real.log ‖ζ - v‖
              + Real.log ‖h ζ‖ : ℝ) : ℂ)) 0 R := by
          apply circleAverage_congr_codiscreteWithin _ hR.ne'
          rw [abs_of_pos hR]
          filter_upwards [(divisor f (sphere 0 R)).eq_zero_codiscreteWithin,
            self_mem_codiscreteWithin (sphere 0 R)] with a ha h₂a
          have hha : h a ≠ 0 := D.ne_zero a (sphere_subset_closedBall h₂a)
          congr 1
          rw [Complex.ofReal_inj, Pi.smul_apply', norm_smul,
            finprod_eq_prod_of_mulSupport_subset (s := h₃f.toFinset) _ (by aesop)]
          simp only [Finset.prod_apply, Pi.pow_apply, norm_prod, norm_zpow]
          rw [Real.log_mul (Finset.prod_ne_zero_iff.2 (hprodne ha)) (norm_ne_zero_iff.2 hha),
            Real.log_prod (hprodne ha)]
          congr 1
          exact Finset.sum_congr rfl fun v _ ↦ log_zpow ‖a - v‖ _
      -- Distribute the kernel over the sum
      _ = circleAverage ((∑ v ∈ h₃f.toFinset, fun ζ ↦ (divisor f (sphere 0 R) v : ℂ) •
              ((2 * ζ / (ζ - w) ^ 2) • (Real.log ‖ζ - v‖ : ℂ)))
            + fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖h ζ‖ : ℂ)) 0 R := by
          apply circleAverage_congr_sphere
          intro a _
          simp only [Pi.add_apply, Finset.sum_apply, smul_eq_mul]
          push_cast
          rw [mul_add, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun v _ ↦ by ring
      -- Integrate term by term
      _ = (∑ v ∈ h₃f.toFinset, (divisor f (sphere 0 R) v : ℂ) •
              circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖ζ - v‖ : ℂ)) 0 R)
            + circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖h ζ‖ : ℂ)) 0 R := by
          rw [circleAverage_add (CircleIntegrable.sum _ ιv) ιh, circleAverage_sum ιv]
          congr 1
          exact Finset.sum_congr rfl fun v _ ↦ circleAverage_fun_smul
      -- Evaluate the boundary terms (B4 special case) and recognise `logDeriv h` (B4)
      _ = (∑ v ∈ h₃f.toFinset, (divisor f (sphere 0 R) v) • (w - v)⁻¹) + logDeriv h w := by
          rw [← MeromorphicOn.logDeriv_eq_circleAverage
            (fun x hx ↦ (D.analyticOnNhd x hx).meromorphicAt)
            (D.analyticOnNhd.mono ball_subset_closedBall)
            (fun z hz ↦ D.ne_zero z (ball_subset_closedBall hz)) hw]
          congr 1
          refine Finset.sum_congr rfl fun v hv ↦ ?_
          rw [circleAverage_smul_log_norm_sub_sphere
            ((divisor f (sphere 0 R)).supportWithinDomain (h₃f.mem_toFinset.1 hv)) hw,
            Int.cast_smul_eq_zsmul]
  -- Final assembly: combine the eventual equalities and evaluate at a point `w`.
  filter_upwards [e₀, e₁, e₂, e₃, self_mem_codiscreteWithin (ball 0 R)]
    with w hw₀ hw₁ hw₂ hw₃ hw
  have hw₂' : logDeriv (∏ᶠ u, canonicalFactor R u ^ (-divisor f (ball 0 R) u)) w
      = ∑ᶠ u, (-divisor f (ball 0 R) u) • logDeriv (canonicalFactor R u) w := hw₂
  have hw₃' : logDeriv (∏ᶠ v, (· - v) ^ divisor f (sphere 0 R) v) w
      = ∑ᶠ v, (divisor f (sphere 0 R) v) • logDeriv (· - v) w := hw₃
  -- The ball sum picks up a sign
  have hs₁ : (∑ᶠ u, (-divisor f (ball 0 R) u) • logDeriv (canonicalFactor R u) w)
      = -∑ᶠ u, (divisor f (ball 0 R) u) • logDeriv (canonicalFactor R u) w := by
    have hsub₁ : (Function.support
        fun u ↦ (-divisor f (ball 0 R) u) • logDeriv (canonicalFactor R u) w)
        ⊆ ↑h₄f.toFinset := by
      intro u hu
      rw [Finite.coe_toFinset]
      exact mem_support.2 fun h₀ ↦ (mem_support.1 hu) (by simp [h₀])
    have hsub₂ : (Function.support
        fun u ↦ (divisor f (ball 0 R) u) • logDeriv (canonicalFactor R u) w)
        ⊆ ↑h₄f.toFinset := by
      intro u hu
      rw [Finite.coe_toFinset]
      exact mem_support.2 fun h₀ ↦ (mem_support.1 hu) (by simp [h₀])
    rw [finsum_eq_sum_of_support_subset _ hsub₁, finsum_eq_sum_of_support_subset _ hsub₂,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun u _ ↦ neg_smul _ _
  -- The sphere sum evaluates to the boundary terms of `key`
  have hs₂ : (∑ᶠ v, (divisor f (sphere 0 R) v) • logDeriv (· - v) w)
      = ∑ v ∈ h₃f.toFinset, (divisor f (sphere 0 R) v) • (w - v)⁻¹ := by
    have hsub₃ : (Function.support fun v ↦ (divisor f (sphere 0 R) v) • logDeriv (· - v) w)
        ⊆ ↑h₃f.toFinset := by
      intro v hv
      rw [Finite.coe_toFinset]
      exact mem_support.2 fun h₀ ↦ (mem_support.1 hv) (by simp [h₀])
    rw [finsum_eq_sum_of_support_subset _ hsub₃]
    exact Finset.sum_congr rfl fun v _ ↦ by rw [logDeriv_id_sub_const]
  change logDeriv f w
      = circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖f ζ‖ : ℂ)) 0 R
        - ∑ᶠ a, (divisor f (ball 0 R) a) • logDeriv (canonicalFactor R a) w
  rw [hw₀, hw₁]
  simp only [Pi.add_apply]
  rw [hw₂', hw₃', hs₁, hs₂, key w hw]
  ring

/-!
## Sanity Check

For `f = id` and `R = 1`, the right-hand side of the differentiated Poisson–Jensen formula
evaluates, at every nonzero point `w` of the unit ball, to `logDeriv id w = w⁻¹`: the kernel
term vanishes because `log ‖·‖ = 0` on the unit circle, the divisor of `id` is a single simple
zero at the origin, and `logDeriv (canonicalFactor 1 0) w = -w⁻¹`.
-/

example {w : ℂ} (hw' : w ≠ 0) :
    circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖(id : ℂ → ℂ) ζ‖ : ℂ)) 0 1
      - ∑ᶠ a, (divisor (id : ℂ → ℂ) (ball 0 1) a) • logDeriv (canonicalFactor 1 a) w
    = logDeriv id w := by
  have hmero : MeromorphicOn (id : ℂ → ℂ) (ball 0 1) := fun x _ ↦ analyticAt_id.meromorphicAt
  -- The kernel term vanishes on the unit circle
  have h₁ : circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • (Real.log ‖(id : ℂ → ℂ) ζ‖ : ℂ)) 0 1
      = 0 := by
    apply circleAverage_const_on_circle
    intro a ha
    rw [abs_one, mem_sphere_zero_iff_norm] at ha
    simp [ha]
  -- The divisor of `id` on the unit ball is a single simple zero at the origin
  have hd₀ : ∀ a : ℂ, a ≠ 0 → divisor (id : ℂ → ℂ) (ball 0 1) a = 0 := by
    intro a ha
    by_cases hab : a ∈ ball (0 : ℂ) 1
    · rw [hmero.divisor_apply hab, analyticAt_id.meromorphicOrderAt_eq,
        analyticAt_id.analyticOrderAt_eq_zero.2 ha]
      rfl
    · by_contra hne
      exact hab ((divisor _ _).supportWithinDomain (mem_support.2 hne))
  have hd₁ : divisor (id : ℂ → ℂ) (ball 0 1) 0 = 1 := by
    rw [hmero.divisor_apply (by simp), meromorphicOrderAt_id]
    rfl
  -- The divisor sum reduces to the canonical factor at the origin
  have h₂ : (∑ᶠ a, (divisor (id : ℂ → ℂ) (ball 0 1) a) • logDeriv (canonicalFactor 1 a) w)
      = logDeriv (canonicalFactor 1 0) w := by
    rw [finsum_eq_single _ 0 (fun a ha ↦ by rw [hd₀ a ha, zero_smul]), hd₁, one_smul]
  -- The logarithmic derivative of the canonical factor at the origin (B5)
  have h₃ : logDeriv (canonicalFactor 1 0) w = -w⁻¹ := by
    rw [Complex.logDeriv_canonicalFactor one_ne_zero hw' (by simp)]
    simp
  rw [h₁, h₂, h₃, logDeriv_apply, deriv_id, id_eq, zero_sub, neg_neg, one_div]
