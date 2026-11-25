/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.JensenFormula

/-!
# The Differentiated Poisson Formula

Let `f : ℂ → ℂ` be meromorphic on the closed ball with center `c` and radius `R`, and analytic
without zeros on the open ball. Zeros and poles on the boundary circle are allowed. This file
shows that the Poisson integral formula holds for `log ‖f ·‖`, and differentiates the formula to
present the logarithmic derivative of `f` as a circle average.

## Main definitions

- `derivHerglotzRieszKernel`: the derivative `2 * (z - c) / (z - w) ^ 2` of the Herglotz–Riesz
  kernel `herglotzRieszKernel c w z` with respect to `w`.

## Main results

- `MeromorphicOn.circleAverage_poissonKernel_smul_log_norm_of_ne_zero`: the Poisson integral
  formula for `log ‖f ·‖`. At every point `w` of the open ball, the Poisson integral of
  `log ‖f ·‖` equals `log ‖f w‖`.
- `MeromorphicOn.logDeriv_eq_circleAverage`: the differentiated Poisson formula. At every point
  `w` of the open ball, `logDeriv f w` is the circle average of `log ‖f ·‖` against
  `derivHerglotzRieszKernel c w`.
- `circleAverage_derivHerglotzRieszKernel_smul_log`: for every point `ρ` of the circle, the circle
  average of `log ‖· - ρ‖` against `derivHerglotzRieszKernel c w` equals `(w - ρ)⁻¹`. This is the
  special case `f = (· - ρ)`, where `f` has a zero on the circle.
- `AnalyticAt.logDeriv_eq_of_eventually_norm_eq`: holomorphic functions with the same norm have
  the same logarithmic derivative.

## Implementation notes

The Herglotz–Riesz integral `F` of `log ‖f ·‖` is holomorphic in the open ball. Its real part is
the Poisson integral of `log ‖f ·‖`, which equals `log ‖f ·‖` by the Poisson integral formula. So
`Complex.exp ∘ F` and `f` have the same norm, hence the same logarithmic derivative, and the
logarithmic derivative of `Complex.exp ∘ F` is the derivative of `F`. This argument does not
require a logarithm of `f`.
-/

@[expose] public section

/-
# Upstreaming plan

Project context: this file is work package B4 of the Lemma on the Logarithmic Derivative, see
`VD/LLD/PLAN-LogarithmicDerivative.md`, §4. Its consumer is the differentiated Poisson–Jensen
formula `MeromorphicOn.logDeriv_eventuallyEq_circleAverage_sub_finsum` in
`VD/LLD/PoissonJensenDeriv.lean` (work package B6).

Status: ready for submission as one PR that touches four Mathlib files. The material depends on
Mathlib master only. It was checked against the Mathlib revision pinned in `lake-manifest.json`
(`e62b985f`, 2026-11-24). On 2026-11-25, the four target files were unchanged on Mathlib master
since that revision, and no open Mathlib PR concerned the Herglotz–Riesz kernel. Two of the
project's open PRs also touch `CircleIntegral.lean`, but not near the place of step 1: #43859
changes the imports and adds `posLog_comp` after `continuousOn_mul`, and #46408 adds a lemma after
`circleIntegrable_congr`.

Each step was type-checked in the context of its target file: with the `open`, `variable` and
`namespace` lines of that file, and with `public section` instead of this project's
`@[expose] public section`.

## Step 1: add one lemma to `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`

`CircleIntegrable.ofReal` goes into the namespace `CircleIntegrable`, directly after
`CircleIntegrable.abs`. There, the declaration is called `ofReal`, and the binders
`{c : ℂ} {R : ℝ}` are dropped, because the target file declares them in a `variable` block.

The lemma replaces an argument that Mathlib spells out by hand. In the proof of
`re_circleAverage_herglotzRieszKernel_smul` in `Mathlib/Analysis/Complex/Poisson.lean`, the three
lines that establish `h₁` can go, with `hg.ofReal` in place of `h₁` in the line that follows. This
is optional; offer it in the PR description and apply it only on request.

## Step 2: add one theorem to `Mathlib/Analysis/Complex/AbsMax.lean`

`AnalyticAt.logDeriv_eq_of_eventually_norm_eq` goes to the end of the section `StrictConvex`,
directly after `eventually_eq_or_eq_zero_of_isLocalMin_norm`. That section sits inside
`namespace Complex`, so the declaration is called
`_root_.AnalyticAt.logDeriv_eq_of_eventually_norm_eq` there. The target file needs no new import.

## Step 3: add the kernel to `Mathlib/Analysis/Complex/Poisson.lean`

The definition `derivHerglotzRieszKernel` and its four lemmas go into the section "Kernels of
Integration", directly after `herglotzRieszKernel_add_const`. The target file needs no new import.

With the kernel in place, `hasDerivAt_circleAverage_herglotzRieszKernel_smul` of the same file
can be restated: its derivative becomes
`circleAverage (fun ζ ↦ derivHerglotzRieszKernel 0 w ζ • f ζ) 0 R`. In its proof, the integrand
`F'` is then `fun x θ ↦ derivHerglotzRieszKernel 0 x (circleMap 0 R θ) • f (circleMap 0 R θ)`, the
cases `meas2` and `bound` unfold the kernel with `derivHerglotzRieszKernel_def`, and the case
`diff` shrinks to an application of `hasDerivAt_herglotzRieszKernel`. After the restatement, the
last line `simp [derivHerglotzRieszKernel_def]` of `MeromorphicOn.logDeriv_eq_circleAverage₀` has
to go. This is optional as well: it makes the statements of the target file consistent, but it
changes a theorem that was merged only recently.

## Step 4: add the main results to `Mathlib/Analysis/Complex/JensenFormula.lean`

The target file gains the line `import Mathlib.Analysis.Complex.AbsMax`. A plain `import` is
enough, because only proofs use it. Everything below the line
`variable {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}` goes to the end of the section "The Poisson-Jensen
Formula", directly after `MeromorphicOn.log_norm_meromorphicTrailingCoeffAt`, unchanged. The
`variable` line itself is dropped, because the target section starts with the same line. The
module docstring of the target file should mention the two formulas.

Why this location. The Poisson integral formula for `log ‖f ·‖` is a corollary of the
Poisson–Jensen formula and belongs next to it. The differentiated formula cannot go to
`Mathlib/Analysis/Complex/Poisson.lean`, where the kernel lives: its proof needs the
Poisson–Jensen formula, and `JensenFormula.lean` imports `Poisson.lean`. The alternative is to let
the private lemma and the two theorems that follow it open the new file
`Mathlib/Analysis/Complex/PoissonJensenDeriv.lean`, the target of
`VD/LLD/PoissonJensenDeriv.lean`. That keeps `JensenFormula.lean` at its present size, but it
creates a file of some 60 lines that stays this small until the differentiated Poisson–Jensen
formula follows, and that PR is blocked by #43985.

## PR title and description (draft)

The description assumes the placement of steps 1–4, without the optional changes; the last
paragraph but one offers them. The paragraphs are wrapped to fit this file. Join the lines of each
paragraph before pasting, because GitHub renders line breaks in PR descriptions.

Title:

    feat(Analysis/Complex): the differentiated Poisson formula

Description:

    Let `f : ℂ → ℂ` be meromorphic on a closed ball, and analytic without zeros on the open ball.
    Zeros and poles on the boundary circle are allowed. Establish the Poisson integral formula for
    `log ‖f ·‖`, and differentiate it: the logarithmic derivative of `f` at a point `w` of the
    open ball is the circle average of `log ‖f ·‖` against the derivative of the Herglotz–Riesz
    kernel with respect to `w`. For `f = (· - ρ)` with `ρ` on the circle, this evaluates the
    circle average to `(w - ρ)⁻¹`, the differentiated counterpart of
    `circleAverage_poissonKernel_smul_log`.

    To this end, add
    - the kernel `derivHerglotzRieszKernel`, together with `hasDerivAt_herglotzRieszKernel`, which
      identifies it as the derivative of `herglotzRieszKernel c w z` with respect to `w`,
    - `AnalyticAt.logDeriv_eq_of_eventually_norm_eq`: holomorphic functions with the same norm
      have the same logarithmic derivative, a consequence of the maximum modulus principle,
    - `CircleIntegrable.ofReal`, the analogue of `MeasureTheory.Integrable.ofReal`.

    The proof of the differentiated formula compares `f` with `Complex.exp ∘ F`, where `F` is the
    Herglotz–Riesz integral of `log ‖f ·‖`. Both functions have the same norm by the Poisson
    integral formula, so they have the same logarithmic derivative, which is the derivative of
    `F`. No logarithm of `f` is needed.

    Two existing declarations in `Mathlib/Analysis/Complex/Poisson.lean` could be adapted to the
    new material: `hasDerivAt_circleAverage_herglotzRieszKernel_smul` could be restated in terms
    of `derivHerglotzRieszKernel`, and the proof of `re_circleAverage_herglotzRieszKernel_smul`
    could be shortened with `CircleIntegrable.ofReal`. Happy to do either here if wanted.

    This material is typically used in complex analysis. The PR will be used in
    [Project VD](https://github.com/kebekus/ProjectVD), formalizing Value Distribution Theory for
    meromorphic functions on the complex plane, in order to establish a proof of the Lemma on the
    Logarithmic Derivative. Claude Code was used to create this PR.

## Step 5: after the merge

- Delete this file and remove `VD.LLD.PoissonSchwarzDeriv` from `VD.lean`.
- In `VD/LLD/PoissonJensenDeriv.lean`, replace the import of this file by
  `Mathlib.Analysis.Complex.JensenFormula`.
- Mark row 5 of the upstreaming table in `VD/LLD/PLAN-LogarithmicDerivative.md` as merged.

## Where the material ends up

| Declaration                                              | Mathlib target        | Visibility |
| -------------------------------------------------------- | --------------------- | ---------- |
| `CircleIntegrable.ofReal`                                | `CircleIntegral.lean` | public     |
| `AnalyticAt.logDeriv_eq_of_eventually_norm_eq`           | `AbsMax.lean`         | public     |
| `derivHerglotzRieszKernel`, `…_def`, `…_fun_def`         | `Poisson.lean`        | public     |
| `derivHerglotzRieszKernel_add_const`                     | `Poisson.lean`        | public     |
| `hasDerivAt_herglotzRieszKernel`                         | `Poisson.lean`        | public     |
| `…circleAverage_poissonKernel_smul_log_norm_of_ne_zero`  | `JensenFormula.lean`  | public     |
| `MeromorphicOn.logDeriv_eq_circleAverage₀`               | `JensenFormula.lean`  | private    |
| `MeromorphicOn.logDeriv_eq_circleAverage`                | `JensenFormula.lean`  | public     |
| `circleAverage_derivHerglotzRieszKernel_smul_log`        | `JensenFormula.lean`  | public     |
-/

open Filter MeromorphicOn Metric Real Topology

/-!
## Circle Integrability
-/

-- The following lemma belongs in `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`; see step 1
-- of the upstreaming plan.

/-- If a real-valued function `f` is circle integrable, then so is `f`, seen as a complex-valued
function. Analogue of `MeasureTheory.Integrable.ofReal`. -/
@[fun_prop]
theorem CircleIntegrable.ofReal {f : ℂ → ℝ} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R) :
    CircleIntegrable (fun z ↦ (f z : ℂ)) c R :=
  ⟨hf.1.ofReal, hf.2.ofReal⟩

/-!
## Holomorphic Functions with the Same Norm
-/

-- The following theorem belongs in `Mathlib/Analysis/Complex/AbsMax.lean`; see step 2 of the
-- upstreaming plan.

/-- If two functions are holomorphic near `x` and have the same norm there, then their logarithmic
derivatives at `x` agree. -/
theorem AnalyticAt.logDeriv_eq_of_eventually_norm_eq {f g : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x)
    (hg : AnalyticAt ℂ g x) (h : ∀ᶠ z in 𝓝 x, ‖f z‖ = ‖g z‖) :
    logDeriv f x = logDeriv g x := by
  have hx : ‖f x‖ = ‖g x‖ := h.self_of_nhds
  obtain hgx | hgx := eq_or_ne (g x) 0
  · simp_all [logDeriv_apply]
  have hfx : f x ≠ 0 := by rwa [← norm_ne_zero_iff, hx, norm_ne_zero_iff]
  -- The quotient `f / g` is holomorphic near `x` and has constant norm, so it is locally constant.
  have h₁ : (fun _ ↦ 1) =ᶠ[𝓝 x] norm ∘ (f / g) := by
    filter_upwards [h, hg.continuousAt.eventually_ne hgx] with z h₁z h₂z
    simp [h₁z, h₂z]
  have h₂ := Complex.eventually_eq_of_isLocalMax_norm
    ((hf.div hg hgx).eventually_analyticAt.mono fun _ h ↦ h.differentiableAt)
    (isLocalMax_const.congr h₁)
  rw [← sub_eq_zero, ← logDeriv_div x hfx hgx hf.differentiableAt hg.differentiableAt,
    (logDeriv_congr_nhds h₂).self_of_nhds]
  simp

/-!
## The Derivative of the Herglotz–Riesz Kernel
-/

-- The following definition and its lemmas belong in `Mathlib/Analysis/Complex/Poisson.lean`; see
-- step 3 of the upstreaming plan.

/-- The derivative of the Herglotz–Riesz kernel `herglotzRieszKernel c w z` with respect to `w`;
see `hasDerivAt_herglotzRieszKernel`. Integrating `log ‖f ·‖` against this kernel yields the
logarithmic derivative of `f`; see `MeromorphicOn.logDeriv_eq_circleAverage`. -/
noncomputable def derivHerglotzRieszKernel (c w z : ℂ) : ℂ := 2 * (z - c) / (z - w) ^ 2

lemma derivHerglotzRieszKernel_def (c w z : ℂ) :
    derivHerglotzRieszKernel c w z = 2 * (z - c) / (z - w) ^ 2 := by rfl

lemma derivHerglotzRieszKernel_fun_def (c w : ℂ) :
    derivHerglotzRieszKernel c w = fun z ↦ 2 * (z - c) / (z - w) ^ 2 := by rfl

lemma derivHerglotzRieszKernel_add_const (c w z : ℂ) :
    derivHerglotzRieszKernel c w (z + c) = derivHerglotzRieszKernel 0 (w - c) z := by
  simp [derivHerglotzRieszKernel_def, sub_sub_eq_add_sub]

/-- Away from its pole, the Herglotz–Riesz kernel `herglotzRieszKernel c w z` is differentiable
in `w`, with derivative `derivHerglotzRieszKernel c w z`. -/
theorem hasDerivAt_herglotzRieszKernel {c w z : ℂ} (hw : w ≠ z) :
    HasDerivAt (herglotzRieszKernel c · z) (derivHerglotzRieszKernel c w z) w := by
  have h₁ : z - c - (w - c) ≠ 0 := by simpa [sub_eq_zero] using hw.symm
  simp only [herglotzRieszKernel_def, derivHerglotzRieszKernel_def]
  convert (((hasDerivAt_id' w).sub_const c).const_add (z - c)).fun_div
    (((hasDerivAt_id' w).sub_const c).const_sub (z - c)) h₁ using 1
  rw [sub_sub_sub_cancel_right]
  ring

/-!
## The Poisson Integral Formula and Its Derivative
-/

-- The remainder of this file belongs in `Mathlib/Analysis/Complex/JensenFormula.lean`; see step 4
-- of the upstreaming plan.

variable {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}

/-- **Poisson integral formula** for `log ‖f ·‖`: if `f` is meromorphic on the closed ball, and
analytic without zeros on the open ball, then the Poisson integral of `log ‖f ·‖` at a point `w`
of the open ball equals `log ‖f w‖`. In contrast to
`InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul`, the function `f` may have
zeros and poles on the boundary circle, where `log ‖f ·‖` is not continuous.

This is the Poisson–Jensen formula `MeromorphicOn.log_norm_meromorphicTrailingCoeffAt` in the
special case where the divisor of `f` on the open ball is trivial. It generalizes
`circleAverage_poissonKernel_smul_log` from `f = (· - ρ)` to arbitrary `f`. -/
theorem MeromorphicOn.circleAverage_poissonKernel_smul_log_norm_of_ne_zero
    (h₁f : MeromorphicOn f (closedBall c R)) (h₂f : AnalyticOnNhd ℂ f (ball c R))
    (h₃f : ∀ z ∈ ball c R, f z ≠ 0) (hw : w ∈ ball c R) :
    circleAverage (poissonKernel c w • (Real.log ‖f ·‖)) c R = Real.log ‖f w‖ := by
  have h₄f {z : ℂ} (hz : z ∈ ball c R) : meromorphicOrderAt f z = 0 :=
    (h₂f z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 (h₃f z hz)
  have h₅f : divisor f (ball c R) = 0 := by
    ext z
    by_cases hz : z ∈ ball c R <;> simp [h₂f.meromorphicOn, hz, h₄f]
  simpa [h₅f, (h₂f w hw).meromorphicTrailingCoeffAt_of_ne_zero (h₃f w hw)] using
    (log_norm_meromorphicTrailingCoeffAt hw (h₄f hw) h₁f).symm

-- Auxiliary lemma for `MeromorphicOn.logDeriv_eq_circleAverage`. The differentiated Poisson
-- formula in the special case where the ball is centred at the origin.
private lemma MeromorphicOn.logDeriv_eq_circleAverage₀
    (h₁f : MeromorphicOn f (closedBall 0 R)) (h₂f : AnalyticOnNhd ℂ f (ball 0 R))
    (h₃f : ∀ z ∈ ball 0 R, f z ≠ 0) (hw : w ∈ ball 0 R) :
    logDeriv f w
      = circleAverage (fun ζ ↦ derivHerglotzRieszKernel 0 w ζ • (Real.log ‖f ζ‖ : ℂ)) 0 R := by
  have hball {z : ℂ} (hz : z ∈ ball 0 R) : z ∉ sphere 0 |R| := by
    grind [mem_sphere, mem_ball, le_abs_self R]
  have hlog : CircleIntegrable (Real.log ‖f ·‖) 0 R :=
    circleIntegrable_log_norm (h₁f.mono_set
      (by simpa [abs_of_pos (pos_of_mem_ball hw)] using sphere_subset_closedBall))
  -- The Herglotz–Riesz integral `F` of `log ‖f ·‖` is holomorphic in the ball. By Poisson's
  -- formula, its real part equals `log ‖f ·‖` there, so that `exp ∘ F` and `f` have the same norm.
  let F := fun z ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 z ζ • (Real.log ‖f ζ‖ : ℂ)) 0 R
  have hF : ∀ᶠ z in 𝓝 w, ‖f z‖ = ‖Complex.exp (F z)‖ := by
    filter_upwards [isOpen_ball.mem_nhds hw] with z hz
    rw [Complex.norm_exp, re_circleAverage_herglotzRieszKernel_smul hlog (hball hz),
      ← poissonKernel_eq_re_herglotzRieszKernel,
      h₁f.circleAverage_poissonKernel_smul_log_norm_of_ne_zero h₂f h₃f hz,
      Real.exp_log (norm_pos_iff.2 (h₃f z hz))]
  -- Hence, `f` and `exp ∘ F` have the same logarithmic derivative, namely the derivative of `F`.
  rw [(h₂f w hw).logDeriv_eq_of_eventually_norm_eq
      (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hlog.ofReal w (hball hw)).cexp' hF,
    logDeriv_apply,
    (hasDerivAt_circleAverage_herglotzRieszKernel_smul hlog.ofReal (hball hw)).cexp.deriv,
    mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  simp [derivHerglotzRieszKernel_def]

/-- **Differentiated Poisson formula**: if `f` is meromorphic on the closed ball, and analytic
without zeros on the open ball, then the logarithmic derivative of `f` at a point `w` of the open
ball is the circle average of `log ‖f ·‖` against the derivative of the Herglotz–Riesz kernel. The
function `f` may have zeros and poles on the boundary circle.

This is the derivative of the Poisson integral formula
`MeromorphicOn.circleAverage_poissonKernel_smul_log_norm_of_ne_zero` with respect to `w`. -/
theorem MeromorphicOn.logDeriv_eq_circleAverage
    (h₁f : MeromorphicOn f (closedBall c R)) (h₂f : AnalyticOnNhd ℂ f (ball c R))
    (h₃f : ∀ z ∈ ball c R, f z ≠ 0) (hw : w ∈ ball c R) :
    logDeriv f w
      = circleAverage (fun ζ ↦ derivHerglotzRieszKernel c w ζ • (Real.log ‖f ζ‖ : ℂ)) c R := by
  -- Reduce to the centred case by translating `f` to `g z = f (z + c)`.
  have hc {z : ℂ} (hz : z ∈ ball 0 R) : z + c ∈ ball c R := by simpa using hz
  have h₁g : MeromorphicOn (fun z ↦ f (z + c)) (closedBall 0 R) := by
    simpa [meromorphicOn_fun_comp_add_const_iff_meromorphicOn] using h₁f
  have key := h₁g.logDeriv_eq_circleAverage₀ (h₂f.comp (by fun_prop) fun _ ↦ hc)
    (fun z hz ↦ h₃f _ (hc hz)) (w := w - c) (by simpa [dist_eq_norm] using hw)
  rw [← circleAverage_map_add_const (c := c)]
  simpa [logDeriv_apply, deriv_comp_add_const, derivHerglotzRieszKernel_add_const] using key

/-- The differentiated Poisson formula for the function `· - ρ`, where `ρ` is a point of the
boundary circle: the circle average of `log ‖· - ρ‖` against the derivative of the Herglotz–Riesz
kernel equals `(w - ρ)⁻¹`, the logarithmic derivative of `· - ρ` at `w`.

This is the derivative of `circleAverage_poissonKernel_smul_log` with respect to `w`. -/
theorem circleAverage_derivHerglotzRieszKernel_smul_log {ρ : ℂ} (hρ : ρ ∈ sphere c R)
    (hw : w ∈ ball c R) :
    circleAverage (fun ζ ↦ derivHerglotzRieszKernel c w ζ • (Real.log ‖ζ - ρ‖ : ℂ)) c R
      = (w - ρ)⁻¹ := by
  rw [← logDeriv_eq_circleAverage (f := (· - ρ)) (by fun_prop) (by fun_prop) (fun z hz ↦ ?_) hw]
  · simp [logDeriv_apply]
  · grind [mem_sphere, mem_ball, sub_ne_zero]
