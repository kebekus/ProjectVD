# Plan: The Lemma on the Logarithmic Derivative

Working plan for formalizing Nevanlinna's *Lemma on the Logarithmic Derivative* (LLD),
in a form that fits the existing Value Distribution library in
`Mathlib/Analysis/Complex/ValueDistribution/` and can be upstreamed as a sequence of
PR-sized pieces. Prepared 2026-07-07 against the Mathlib checkout in `.lake`
(commit of 2026-07-07).

---

## 1. Goal

**Classical statement.** For `f` meromorphic on `ℂ`,

```
m(r, f′/f) = O( log⁺ T(r, f) + log r )   as r → ∞, outside a set of finite Lebesgue measure.
```

This is the key analytic input for the Second Main Theorem. References:

- Lang, *Introduction to Complex Hyperbolic Spaces* [MR886677], Ch. VI
  (pin the exact section number from the book when writing doc-strings);
- Lang–Cherry, *Topics in Nevanlinna Theory*, Springer LNM 1433, Ch. I
  (sharp error terms; a good model for the two-radius estimate);
- Hayman, *Meromorphic Functions*, §3.1 (classical proof);
- Cherry–Ye, *Nevanlinna's Theory of Value Distribution*, Ch. 3
  (Gol'dberg–Grinshtein-type sharp constants — an optional refinement, not the target).

**Formal target.** Three theorems, in decreasing order of "quantitativeness":

```lean
-- (T1) Two-radius estimate: fully exceptional-set-free, the analytic core.
theorem ValueDistribution.exists_proximity_logDeriv_le {f : ℂ → ℂ} (hf : Meromorphic f) :
    ∃ c, ∀ r R, 1 ≤ r → r < R →
      proximity (logDeriv f) ⊤ r
        ≤ c * (log⁺ (characteristic f ⊤ R) + log R + log⁺ (R - r)⁻¹ + 1)

-- (T2) Borel growth lemma: pure real analysis, no complex analysis at all.
theorem MonotoneOn.eventually_le_two_mul {S : ℝ → ℝ} {a : ℝ}
    (h₁ : MonotoneOn S (Set.Ici a)) (h₂ : ∀ r ∈ Set.Ici a, 1 ≤ S r) :
    ∀ᶠ r in volume.cofinite ⊓ atTop, S (r + (S r)⁻¹) ≤ 2 * S r

-- (T3) The Lemma on the Logarithmic Derivative.
theorem ValueDistribution.isBigO_proximity_logDeriv {f : ℂ → ℂ} (hf : Meromorphic f) :
    proximity (logDeriv f) ⊤ =O[volume.cofinite ⊓ atTop]
      fun r ↦ log⁺ (characteristic f ⊤ r) + log r
```

Plus a corollary with **no exceptional set** for functions of finite order
(cheap from T1 with `R := 2 * r`, no Borel lemma needed — a good intermediate milestone):

```lean
theorem ValueDistribution.isBigO_proximity_logDeriv_of_isBigO_rpow {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Meromorphic f) (h : characteristic f ⊤ =O[atTop] (· ^ ρ)) :
    proximity (logDeriv f) ⊤ =O[atTop] Real.log
```

### Design decisions (and why)

1. **`m(r, f′/f)` is `proximity (logDeriv f) ⊤ r`.** Mathlib's `logDeriv f = deriv f / f`
   (`Mathlib/Analysis/Calculus/LogDeriv.lean`) is exactly `f′/f`, and
   `Meromorphic.logDeriv : Meromorphic f → Meromorphic (logDeriv f)` already exists.
   `logDeriv f` takes junk values where `f` is not differentiable, but `proximity` only
   sees the codiscrete equivalence class, so this is harmless.

2. **Exceptional set = the filter `volume.cofinite ⊓ atTop`.**
   `MeasureTheory.Measure.cofinite` exists (`mem_cofinite : s ∈ μ.cofinite ↔ μ sᶜ < ∞`,
   `eventually_cofinite`), so "for all large `r` outside a set of finite measure" is
   literally `∀ᶠ r in volume.cofinite ⊓ atTop`. No new filter needed. This gives clean
   `IsBigO` statements in the style of `isBigO_characteristic_sub_characteristic_inv`.

3. **No nondegeneracy hypothesis in the final statements.** If `f ≡ 0` away from a
   discrete set (`meromorphicOrderAt f = ⊤` everywhere), then `logDeriv f = 0` on a
   codiscrete open set, `proximity (logDeriv f) ⊤ r = 0` for `r ≠ 0`, and all statements
   hold trivially. Handle this case first in the proofs
   (`Meromorphic.exists_meromorphicOrderAt_eq_top_iff_forall`, already in
   `VD/MathlibPending/CharacteristicMoebius.lean`, does the case split).

4. **Right-hand side uses `log⁺ (characteristic …)`,** not `log (characteristic …)`:
   `characteristic` is only eventually nonnegative and can be bounded (rational `f`),
   so `log⁺` avoids sign traps inside `IsBigO`. The `+ log r` term dominates in the
   rational case, so T3 is meaningful for every meromorphic `f`.

5. **Constants.** T1 carries a single existential constant `c` (depending on `f` through
   `log ‖f 0‖`, `log ‖meromorphicTrailingCoeffAt f 0‖`, i.e. the same normalization data
   already appearing in the First Main Theorem). An absolute-constant version à la
   Gol'dberg–Grinshtein is *not* the target; it can be refined later if ever needed.

6. **Proof route** = classical Nevanlinna/Lang route:
   differentiated Poisson–Jensen formula → pointwise bound on `|f′/f|` on the circle
   `|z| = r` in terms of data at radius `ρ = (r+R)/2` → integrate `log⁺` using concavity
   of `log` and the exponent-`1/2` trick for the sum over zeros/poles → Borel growth
   lemma to eliminate the second radius. Every analytic ingredient is either already in
   Mathlib or isolated below as a named work item.

---

## 2. Inventory

### Already available (verified in the 2026-07-07 checkout)

| Ingredient | Name(s) |
|---|---|
| VD functions & FMT | `ValueDistribution.proximity/logCounting/characteristic`, `characteristic_sub_characteristic_inv_le`, `abs_characteristic_sub_characteristic_shift_le` |
| Monotonicity of `T` | `ValueDistribution.characteristic_monotoneOn` (Cartan.lean) |
| `logDeriv` calculus | `logDeriv_apply/_mul/_div/_prod/_fun_zpow/_comp`, `Meromorphic.logDeriv`, `MeromorphicOn.logDeriv` |
| Meromorphic derivatives | `MeromorphicAt.deriv`, `meromorphicOrderAt_deriv_eq_sub_one`, `meromorphicOrderAt_div/_inv/_mul` |
| Canonical factors | `Complex.canonicalFactor` + full API (`norm_canonicalFactor_eval_circle_eq_one`, `divisor_canonicalFactor`, …), `CanonicalDecomp`, `MeromorphicOn.exists_canonicalDecomp` |
| Extended decomposition | `ECanonicalDecomp`, `exists_ecanonicalDecomp` (local, `VD/MathlibSubmitted/BlaschkeDecomp2.lean` — PR in flight) |
| Poisson–Jensen | `MeromorphicOn.log_norm_meromorphicTrailingCoeffAt` (local, `VD/MathlibPending/PoissonJensen.lean`) |
| Herglotz–Riesz kernel | `herglotzRieszKernel` + bounds `re_herglotzRieszKernel_le`, `le_re_herglotzRieszKernel`; Poisson representation for `DiffContOnCl` and `HarmonicOnNhd` |
| Cauchy integrals of L¹ data | `Complex.hasFPowerSeriesOn_cauchy_integral` (analyticity in the pole for merely `CircleIntegrable f`) |
| Differentiation under ∫ | `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`ParametricIntegral.lean`, `𝕜 = ℂ` via `RCLike`) |
| Analytic-completion tools | `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`, `AnalyticOnNhd.eq_const_of_re_eq_const`, `DifferentiableOn.isExactOn_ball` (primitives on balls), `AnalyticAt.harmonicAt_log_norm` |
| `log⁺` toolkit | `posLog_mul/_add/_sum/_prod/_pow`, `posLog_sub_posLog_inv`, `half_mul_log_add_log_abs`, `posLog_norm_sum_le` |
| Exact circle averages | `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`, `…_of_mem_closedBall`, Jensen `MeromorphicOn.circleAverage_log_norm` |
| Integrability | `MeromorphicOn.circleIntegrable_log_norm/_posLog_norm`, `intervalIntegrable_rpow'` (exponent > −1) |
| Jensen inequality (integral) | `ConcaveOn.le_map_average` / `le_map_integral` + `strictConcaveOn_log_Ioi`; `circleAverage_eq_intervalAverage` |
| Exceptional-set filter | `MeasureTheory.Measure.cofinite` |
| Covering lemma | `Vitali.exists_disjoint_subfamily_covering_enlargement(_closedBall)` |
| Jordan inequality | `Real.mul_le_sin : 2/π * x ≤ sin x` on `[0, π/2]` |

### Missing (= the actual work, grouped into work packages A–E below)

- ~~meromorphic order/congruence/arithmetic API for `logDeriv` (A)~~ ✅ done;
- ~~`posLog_rpow`, `abs_log_eq_posLog_add_posLog_inv` (A)~~ ✅ done;
- ~~derivative of the Cauchy integral in the pole variable (B1)~~ ✅ done (with B2–B3);
- ~~differentiated Poisson(–Schwarz) representation for ball-nonvanishing functions (B4)~~ ✅ done;
- ~~`logDeriv` of `canonicalFactor` + bounds (B5)~~ ✅ done;
- ~~differentiated Poisson–Jensen formula (B6)~~ ✅ done;
- ~~uniform circle-average bound for `‖· − a‖^(−1/2)` (C2)~~ ✅ done;
- ~~concavity estimate `circleAverage log⁺ u ≤ log⁺ (circleAverage u) + log 2` (C1)~~ ✅ done;
- ~~unintegrated counting function vs. `logCounting` (C3)~~ ✅ done;
- ~~the two-radius estimate T1 (C4)~~ ✅ done;
- ~~the Borel growth lemma T2 (D)~~ ✅ done;
- ~~final assembly T3 + corollaries (E)~~ ✅ done.

**All work packages are complete (2026-07-08); the Lemma on the Logarithmic Derivative is
fully formalized.** Remaining: upstreaming (see §8) and the post-LLD items (§10).

---

## 3. Work package A — meromorphic API for `logDeriv`

**✅ DONE (2026-07-07).** Implemented in `VD/LLD/MeromorphicLogDeriv.lean` and
`VD/LLD/PosLog.lean`; compiles lint-clean. Deviations from the sketch below: statements are in
Mathlib-ready generality (`𝕜 → 𝕜'` where possible; order lemmas over `𝕜 → 𝕜` with
`[CompleteSpace 𝕜] [CharZero 𝕜]`); added the helper `MeromorphicOn.ne_zero_mem_codiscreteWithin`
and, beyond `logDeriv_mul_eventuallyEq`, the `Finset`/`finprod`/`zpow` versions including the
B6-shaped `logDeriv_finprod_zpow_eventuallyEq` (divisor-style `ℤ`-exponents).

*New file, eventually `Mathlib/Analysis/Meromorphic/LogDeriv.lean`
(locally: `VD/LLD/MeromorphicLogDeriv.lean`). Independent of everything else.*

```lean
-- pointwise meromorphy (one-liner: h.deriv.div h)
theorem MeromorphicAt.logDeriv {f : ℂ → ℂ} (h : MeromorphicAt f x) :
    MeromorphicAt (logDeriv f) x

-- the crucial structural fact: logDeriv has at worst SIMPLE poles.
-- At zeros/poles of f (order n ∉ {0, ⊤}): order (logDeriv f) = −1
theorem meromorphicOrderAt_logDeriv_eq_neg_one {f : ℂ → ℂ}
    (hf : MeromorphicAt f x) (h₁ : meromorphicOrderAt f x ≠ 0)
    (h₂ : meromorphicOrderAt f x ≠ ⊤) :
    meromorphicOrderAt (logDeriv f) x = -1
  -- proof: meromorphicOrderAt_div + meromorphicOrderAt_deriv_eq_sub_one
  --        (char-0 hypothesis is automatic over ℂ)

-- at order-0 points, logDeriv is analytic-in-the-NF-sense:
theorem meromorphicOrderAt_logDeriv_nonneg {f : ℂ → ℂ}
    (hf : MeromorphicAt f x) (h : meromorphicOrderAt f x = 0) :
    0 ≤ meromorphicOrderAt (logDeriv f) x

-- congruence: logDeriv only depends on the codiscrete class (equality on an open
-- codiscrete set gives equality of derivatives there)
theorem logDeriv_congr_codiscreteWithin {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h : f =ᶠ[codiscreteWithin U] g) :
    logDeriv f =ᶠ[codiscreteWithin U] logDeriv g

-- arithmetic, codiscrete versions (the pointwise logDeriv_mul needs nonvanishing;
-- for meromorphic f, g of order ≠ ⊤ the bad set is discrete):
theorem logDeriv_mul_eventuallyEq {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g)
    (h'f : ∀ x, meromorphicOrderAt f x ≠ ⊤) (h'g : ∀ x, meromorphicOrderAt g x ≠ ⊤) :
    logDeriv (f * g) =ᶠ[codiscrete ℂ] logDeriv f + logDeriv g
-- + finprod and zpow versions, localized (codiscreteWithin U) as needed for B6
```

Also fold in the two tiny `posLog` gaps (target `Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean`):

```lean
theorem Real.posLog_rpow (hx : 0 ≤ x) (hα : 0 ≤ α) : log⁺ (x ^ α) = α * log⁺ x
theorem Real.abs_log_eq_posLog_add_posLog_inv : |log x| = log⁺ x + log⁺ x⁻¹
  -- from half_mul_log_add_log_abs and posLog_sub_posLog_inv
```

Notes:
- *Not needed for the LLD:* `divisor (logDeriv f)` computations and
  `N(r, f′/f)`-type bounds. They will matter for the Second Main Theorem
  (through `N̄`), but keep them out of scope here to keep the PR small.
- Estimated size: ~250 lines. Difficulty: low.

---

## 4. Work package B — the differentiated Poisson–Jensen formula

*The complex-analytic heart. Target statement (centered at 0, which is all that
value distribution needs; general center can be added later by translation):*

```lean
/-- **Differentiated Poisson–Jensen formula**: away from a discrete set, the
logarithmic derivative of a meromorphic function on `closedBall 0 R` is the circle
average of `log ‖f ·‖` against the `w`-derivative of the Herglotz–Riesz kernel,
corrected by the logarithmic derivatives of the canonical factors. -/
theorem MeromorphicOn.logDeriv_eqOn_codiscrete {f : ℂ → ℂ} {R : ℝ}
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : closedBall (0 : ℂ) R, meromorphicOrderAt f u ≠ ⊤) :
    logDeriv f =ᶠ[codiscreteWithin (ball 0 R)]
      fun w ↦ circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • Real.log ‖f ζ‖) 0 R
        - ∑ᶠ a, (divisor f (ball 0 R) a) • logDeriv (canonicalFactor R a) w
```

Sign check (`f = id`, `R = 1`): `divisor = δ₀`, `canonicalFactor 1 0 = (·)⁻¹`,
`logDeriv (·⁻¹) w = −1/w`, kernel term `= 0`; RHS `= 0 − (−1/w) = 1/w = logDeriv id w`. ✓
(The sign is `−Σ` because `ECanonicalDecomp` uses `canonicalFactor ^ (−divisor)`.)

The classical shape is recovered via B5:
`logDeriv (canonicalFactor R a) w = −((w − a)⁻¹ + conj a / (R² − conj a * w))`.

**✅ B1–B3 DONE (2026-07-07).** Implemented in `VD/LLD/CauchyIntegralDeriv.lean`; compiles
lint-clean, ~230 lines. Deviations from the sketch below: B2/B3 are stated for the integrand
`fun ζ ↦ herglotzRieszKernel 0 w ζ • g ζ` with `g` valued in a complex Banach space (B4 will
instantiate `g := fun ζ ↦ (log ‖h ζ‖ : ℂ)`); B3 carries the extra hypothesis `w ∈ ball 0 R`
(needed for integrability — without it the statement is false when only the real part of the
integrand is integrable); B2's derivative is proved directly by the dominated-derivative theorem
(not via B1 and partial fractions), and the analyticity record comes as corollaries
`differentiableOn_/analyticOnNhd_circleAverage_herglotzRieszKernel_smul` via
`DifferentiableOn.analyticOnNhd` rather than `hasFPowerSeriesOn_cauchy_integral`. The kernel's
continuity on the sphere is proved inline (private lemma) to keep the file independent of the
pending Poisson–Jensen chain.

### B1. Derivative of the Cauchy integral (new, Mathlib-worthy on its own)

```lean
theorem hasDerivAt_circleIntegral_sub_inv_smul {g : ℂ → E}
    (hg : CircleIntegrable g c R) (hw : w ∈ ball c R) :
    HasDerivAt (fun w ↦ ∮ z in C(c, R), (z - w)⁻¹ • g z)
      (∮ z in C(c, R), ((z - w) ^ 2)⁻¹ • g z) w
```

Proof: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` over `𝕜 = ℂ`
(parametrize by `θ ∈ [0, 2π]`; the integrand is smooth in `w` with derivative
dominated by `C_K · ‖g (circleMap c R θ)‖` on a closed sub-ball, which is
interval-integrable). Complements `hasFPowerSeriesOn_cauchy_integral`, which
already gives analyticity but not this closed form at off-center points.

### B2–B3. The kernel integral and its derivative/real part

For real `g` with `CircleIntegrable g 0 R`, set `F g w := circleAverage (herglotzRieszKernel 0 w • g) 0 R`.
Using `herglotzRieszKernel 0 w ζ = 2 * ζ * (ζ - w)⁻¹ - 1` and
`circleAverage_eq_circleIntegral`, `F g` is (up to a constant) a Cauchy integral of
`ζ ↦ 2ζ • g ζ`. Record:

```lean
-- analyticity on the ball  (from hasFPowerSeriesOn_cauchy_integral)
-- derivative:
theorem hasDerivAt_circleAverage_herglotzRieszKernel_smul
    (hg : CircleIntegrable g 0 R) (hw : w ∈ ball 0 R) :
    HasDerivAt (fun w ↦ circleAverage (herglotzRieszKernel 0 w • g) 0 R)
      (circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • g ζ) 0 R) w
-- real part (Re commutes with the integral):
theorem re_circleAverage_herglotzRieszKernel_smul (hg : CircleIntegrable g 0 R) :
    (circleAverage (herglotzRieszKernel 0 w • g) 0 R).re
      = circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 R
```

**✅ B4–B5 DONE (2026-07-07).** Implemented in `VD/LLD/PoissonSchwarzDeriv.lean` (~230 lines);
compiles lint-clean. Deviations from the sketches below: B4 is named
`MeromorphicOn.logDeriv_eq_circleAverage` (dot notation on the closed-ball meromorphy); its proof
follows steps 1–4 exactly, with step 1's analyticity from the B2 corollary
`analyticOnNhd_circleAverage_herglotzRieszKernel_smul` and step 3's constant obtained via
`IsOpen.exists_is_const_of_deriv_eq_zero` applied to `h · exp (−G)`. The boundary special case is
`circleAverage_smul_log_norm_sub_sphere`. B5's `Complex.logDeriv_canonicalFactor` carries the
additional (necessary) hypothesis `R ≠ 0`; the norm bound
`Complex.norm_logDeriv_canonicalFactor_le` needs no `w ≠ a` hypothesis — at `w = a` both sides
degenerate gracefully (`0 ≤ …` by the junk-value conventions).

### B4. Differentiated Poisson representation for ball-nonvanishing functions

```lean
/-- If `h` is meromorphic on the closed ball, analytic and nonvanishing on the open
ball, its logarithmic derivative is the circle average of `log ‖h ·‖` against the
derived kernel. -/
theorem logDeriv_eq_circleAverage {h : ℂ → ℂ} (h₁ : MeromorphicOn h (closedBall 0 R))
    (h₂ : AnalyticOnNhd ℂ h (ball 0 R)) (h₃ : ∀ z ∈ ball 0 R, h z ≠ 0)
    (hw : w ∈ ball 0 R) :
    logDeriv h w = circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • Real.log ‖h ζ‖) 0 R
```

Proof sketch (all tools exist):
1. `F := F (log ‖h ·‖)` is analytic on the ball with the derivative from B2–B3;
   integrability from `MeromorphicOn.circleIntegrable_log_norm`.
2. `Re (F w) = log ‖h w‖` for `w ∈ ball`: apply the (pending) Poisson–Jensen theorem
   `MeromorphicOn.log_norm_meromorphicTrailingCoeffAt` to `h` — the divisor term
   vanishes since `h` has no zeros/poles in the ball, and
   `meromorphicTrailingCoeffAt h w = h w` at analytic nonvanishing points.
3. `logDeriv h` is analytic on the ball and has a primitive `G` there
   (`DifferentiableOn.isExactOn_ball`); then `(h · exp (−G))′ = 0`, so `h = κ · exp G`
   on the connected ball with `κ ≠ 0`, hence `Re G = log ‖h ·‖ − log |κ|`.
4. `F − G` is analytic with constant real part `log |κ|`, hence constant
   (`AnalyticOnNhd.eq_const_of_re_eq_const`); differentiate: `F′ = G′ = logDeriv h`. ∎

Crucially, `h₃` is required only on the **open** ball, so B4 applies both to the
`ECanonicalDecomp` remainder `h` *and* to `h = (· − u)` with `u` on the **sphere** —
which yields the boundary-divisor correction for free:

```lean
-- special case, u ∈ sphere 0 R, w ∈ ball 0 R:
--   circleAverage (fun ζ ↦ (2ζ/(ζ−w)²) • log ‖ζ − u‖) 0 R = (w − u)⁻¹
```

### B5. `logDeriv` of the canonical factor

```lean
theorem Complex.logDeriv_canonicalFactor {a w : ℂ} (hw₁ : w ≠ a)
    (hw₂ : (R:ℂ)^2 - conj a * w ≠ 0) :
    logDeriv (canonicalFactor R a) w = -((w - a)⁻¹ + conj a / (R ^ 2 - conj a * w))

-- the bound used in C4: for ‖a‖ < ρ and ‖w‖ = r < ρ,
theorem Complex.norm_logDeriv_canonicalFactor_le … :
    ‖logDeriv (canonicalFactor ρ a) w‖ ≤ ‖w - a‖⁻¹ + (ρ - r)⁻¹
  -- since ‖ρ² − conj a * w‖ ≥ ρ² − ‖a‖·r > ρ(ρ − r)
```

### B6. Assembly of the differentiated Poisson–Jensen formula

**✅ DONE (2026-07-08).** Implemented in `VD/LLD/PoissonJensenDeriv.lean` (~330 lines); compiles
lint-clean. Deviations from the sketch below: the statement writes the integrand with an explicit
complex cast, `(2 * ζ / (ζ - w) ^ 2) • (Real.log ‖f ζ‖ : ℂ)`, matching B4; no positivity
hypothesis on `R` (for `R ≤ 0` the ball is empty and the statement is vacuous). The proof follows
steps 1–3 exactly, with the package-A lemma `logDeriv_finprod_zpow_eventuallyEq` expanding both
finprods; order-≠-⊤ bookkeeping for the product factors runs through `meromorphicOrderAt_prod`,
`meromorphicOrderAt_zpow` and `WithTop.sum_ne_top/mul_ne_top`. Private helpers: continuity and
integrability of the derived kernel `2ζ/(ζ−w)²` on the sphere, `meromorphicOrderAt (· - v) ≠ ⊤`,
and `logDeriv (· - v) w = (w - v)⁻¹`. The sphere-divisor cancellation works as predicted via
`circleAverage_smul_log_norm_sub_sphere`.

Mirror the proof of `poissonJensen₀` in `VD/MathlibPending/PoissonJensen.lean`:

1. Take the extended decomposition
   `f =ᶠ[codiscreteWithin closedBall] (∏ᶠ cF^(−D_ball)) * (∏ᶠ (· − u)^(D_sphere)) • h`
   (`exists_ecanonicalDecomp`; the degenerate `order = ⊤` case is excluded by `h₂f`).
2. Apply the codiscrete `logDeriv` arithmetic from package A:
   `logDeriv f =ᶠ[codiscreteWithin ball] −Σᶠ D_ball • logDeriv cF + Σᶠ D_sphere • logDeriv (· − u) + logDeriv h`.
3. Rewrite `logDeriv h` by B4; on the sphere,
   `log ‖h‖ =ᵃᵉ log ‖f‖ − Σ D_ball · log ‖cF‖ − Σ D_sphere · log ‖· − u‖`,
   where the `cF` terms vanish (`norm_canonicalFactor_eval_circle_eq_one`) and each
   sphere term integrates to `(w − u)⁻¹` by the B4 special case — cancelling the
   `Σ D_sphere` terms from step 2 exactly. (Same cancellation pattern as in the
   existing Poisson–Jensen proof, with `logDeriv` in place of `log ‖·‖`.)

Estimated size: B1–B3 ≈ 250 lines; B4–B5 ≈ 250 lines; B6 ≈ 300–400 lines
(finsum/divisor bookkeeping dominates; the pattern is established in PoissonJensen.lean).
Difficulty: B6 medium-high (bookkeeping), everything else low-medium.

---

## 5. Work package C — circle-average estimates and the two-radius bound (T1)

**✅ C1–C3 DONE (2026-07-07).** C1–C2 implemented in `VD/LLD/CircleAverageEstimates.lean`
(~340 lines), C3 in `VD/LLD/CountingEstimate.lean` (~150 lines); both compile lint-clean.
Deviations from the sketches below:

- **C2** needs no case split at all: the estimate
  `‖circleMap 0 r (θ + arg a) − a‖ ≥ (r/2)·|sin (θ/2)|` holds for **every** `a : ℂ`
  (via `‖circleMap 0 r θ − s‖² = (r−s)² + 4rs·sin²(θ/2)` for `s = ‖a‖ ≥ 0`, linear in `sin²`),
  so a single Jordan-inequality majorant
  `(r/(2π)·θ)^(−1/2) + (r/(2π)·(2π−θ))^(−1/2)` covers all base points. Its integral is exactly
  `8π·r^(−1/2)`, giving the explicit absolute constant `C = 4`. Integrability for arbitrary
  radii (`r < 0`, `r = 0`) is reduced to `r > 0` via `Function.Periodic.intervalIntegrable₀`
  and angle shifts.
- **C3** is stated in the `Function.locallyFinsuppWithin` namespace (where `logCounting` for
  divisors actually lives); the helper `Real.sub_div_le_log_div : (r − ρ)/r ≤ log (r/ρ)` is
  included there. The FMT specialisation is deferred to C4, where characteristic/proximity are
  in scope.

### C1. Concavity: averages of `log⁺`

```lean
/-- Jensen's inequality specialised to circle averages: for nonnegative
circle-integrable `u`, the average of `log⁺ u` is at most `log⁺` of the average,
up to `log 2`. -/
theorem Real.circleAverage_posLog_le_posLog_circleAverage {u : ℂ → ℝ}
    (h₀ : ∀ z ∈ sphere 0 |r|, 0 ≤ u z) (hu : CircleIntegrable u 0 r) :
    circleAverage (log⁺ ∘ u) 0 r ≤ log⁺ (circleAverage u 0 r) + Real.log 2
```

Proof: `log⁺ x ≤ log (1 + x) ≤ log⁺ x + log 2` for `x ≥ 0`; concavity of
`log (1 + ·)` on the closed set `Ici 0` via `ConcaveOn.le_map_average`
(`strictConcaveOn_log_Ioi`, shifted), transported through
`circleAverage_eq_intervalAverage`. Watch the hypotheses of `le_map_average`:
closed target set, a.e. membership, integrability of `u` and `log (1 + u ·)` —
all satisfied here.

### C2. Uniform bound for the singular sum (the exponent-1/2 trick)

```lean
/-- Uniformly in `a : ℂ`, the circle average of `‖· − a‖^(−1/2)` over the circle of
radius `r > 0` is bounded by `C / √r` for an absolute constant `C`. -/
theorem Real.circleIntegrable_norm_sub_rpow (a : ℂ) (r : ℝ) :
    CircleIntegrable (‖· - a‖ ^ (-(2: ℝ)⁻¹)) 0 r

theorem Real.circleAverage_norm_sub_rpow_le {a : ℂ} (hr : 0 < r) :
    circleAverage (‖· - a‖ ^ (-(2: ℝ)⁻¹)) 0 r ≤ C * r ^ (-(2: ℝ)⁻¹)
```

Proof sketch: split on `|‖a‖ − r| ≥ r/2` (then `‖z − a‖ ≥ r/2` on the circle, trivial)
vs. `r/2 < ‖a‖ < 3r/2`; in the latter case
`‖circleMap 0 r θ − a‖² = r² + ‖a‖² − 2r‖a‖cos(θ − θ₀) ≥ 4r‖a‖ sin²((θ−θ₀)/2) ≥ 2r² sin²((θ−θ₀)/2)`,
then `Real.mul_le_sin` (Jordan) and `intervalIntegrable_rpow'` (exponent `−1/2 > −1`)
finish. This is where the classical proof's `|Σ 1/(z−a)|^{1/2} ≤ Σ |z−a|^{−1/2}`
device pays off: the bound is *uniform in `a`*, unlike the average of `‖·−a‖⁻¹`.

### C3. Unintegrated counting function

```lean
/-- The total mass of a nonnegative divisor on `closedBall 0 ρ`, weighted by
`log (r/ρ)`, is bounded by the logarithmic counting function at radius `r`. -/
theorem Function.locallyFinsupp.sum_toClosedBall_le_logCounting
    {D : locallyFinsupp ℂ ℤ} (hD : 0 ≤ D) (hρ : 1 ≤ ρ) (hρr : ρ < r) :
    (∑ᶠ z, (D.toClosedBall ρ z : ℝ)) * Real.log (r / ρ) ≤ D.logCounting r
```

(Each `z` with `‖z‖ ≤ ρ` contributes at least `D z · log (r/ρ)` to
`logCounting D r = ∑ᶠ z, D.toClosedBall r z * log (r‖z‖⁻¹) + D 0 * log r`;
the origin convention is handled by the compensating summand, cf. the
implementation note in `LogCounting/Basic.lean`.) Then specialize to
`D = (divisor f univ)⁺ + (divisor f univ)⁻` and connect to
`logCounting f 0 + logCounting f ⊤ ≤ 2 · characteristic f ⊤ r + O(1)`
(First Main Theorem). Also needed: `log (R/ρ) ≥ (R − ρ)/R`
(from `Real.log_le_sub_one_of_pos` applied to `ρ/R`), turning `1/log(R/ρ)` into
the error terms `log R + log⁺ (R − ρ)⁻¹`.

### C4. The two-radius estimate (theorem T1)

**✅ DONE (2026-07-08).** Implemented in `VD/LLD/LogDerivTwoRadius.lean` (~690 lines); compiles
lint-clean. `ValueDistribution.exists_proximity_logDeriv_le` is stated exactly as T1. Deviations
from the sketch below: steps 1–4 are packaged into one private lemma `proximity_logDeriv_le`
producing `m(r) ≤ 2·log⁺(√K + n·(4 + (ρ−r)^(−1/2))) + 2 log 2` (the constant `4` is C2's explicit
constant); steps 5 and 6 are separate private lemmas (`circleAverage_abs_log_norm_le`,
`finsum_abs_divisor_le`), both bounding by `2·T(R) + c_f` with `c_f` the FMT constant. A private
helper `circleAverage_mono_codiscreteWithin` compares circle averages of functions that satisfy
`≤` only away from a discrete set (needed since B6 holds only codiscretely); further private
helpers: `√`-subadditivity (binary and over `Finset.sum`, absent from Mathlib and worth
upstreaming), `norm_circleAverage_le`, and `posLog_le_abs` (duplicated from C1's private part).
The final constant is `c := 5 + 22·log 2 + 3·log⁺ c_f`. The degenerate case uses
`exists_meromorphicOrderAt_eq_top_iff_eventually_zero` from `VD/MathlibPending/`, so the T1 file
currently depends on the CharacteristicMoebius pending chain in addition to files 1, 6, 7, 8.

Fix `1 ≤ r < R`, set `ρ := (r + R)/2`, `n := ∑ᶠ |divisor f (ball 0 ρ)|`,
`K := (2ρ/(ρ−r)²) · circleAverage |log ‖f ·‖| 0 ρ`. Chain of estimates, each a
lemma-sized step:

1. **A.e. pointwise bound on the circle `|w| = r`** (from B6 + B5):
   `‖logDeriv f w‖ ≤ K + Σᶠ_a |D a| · (‖w − a‖⁻¹ + (ρ−r)⁻¹)`.
2. **Square-root split:** `‖logDeriv f w‖^{1/2} ≤ K^{1/2} + Σ_a |D a| (‖w−a‖^{−1/2} + (ρ−r)^{−1/2})`
   (using `√(x+y) ≤ √x + √y`, `√(mx) ≤ m√x` for integers `m ≥ 1`).
3. **Integrate** with C2:
   `circleAverage ‖logDeriv f ·‖^{1/2} ≤ K^{1/2} + n·(C r^{−1/2} + (ρ−r)^{−1/2})`.
4. **Concavity** (C1, applied to the explicit bound function, whose circle
   integrability is termwise — this avoids any new "rpow of meromorphic norm"
   integrability theory):
   `proximity (logDeriv f) ⊤ r = circleAverage (log⁺ ‖logDeriv f ·‖) 0 r
     = 2 · circleAverage (log⁺ (‖logDeriv f ·‖^{1/2})) 0 r
     ≤ 2 log⁺ (K^{1/2} + n (C r^{−1/2} + (ρ−r)^{−1/2})) + 2 log 2`
   then expand with `posLog_add`, `posLog_mul`, `posLog_rpow`.
5. **Bound `K`:** `circleAverage |log ‖f ·‖| 0 ρ = proximity f ⊤ ρ + proximity f⁻¹ ⊤ ρ
     ≤ 2 · characteristic f ⊤ R + c_f`
   (via `abs_log_eq_posLog_add_posLog_inv`, `proximity_inv`, `m ≤ T`,
   FMT `characteristic_sub_characteristic_inv_le`, and `characteristic_monotoneOn`).
6. **Bound `n`** with C3 at radii `ρ < R`.
7. Collect: everything is `≤ c · (log⁺ (characteristic f ⊤ R) + log R + log⁺ (R−r)⁻¹ + 1)`.

Degenerate case `∀ x, meromorphicOrderAt f x = ⊤`: LHS is `0` for `r ≥ 1`, statement
trivial (see design decision 3).

Estimated size: C1 ≈ 80, C2 ≈ 150, C3 ≈ 80, C4 ≈ 250–350 lines.
Difficulty: C4 medium (long but mechanical once 1–6 are in place).

---

## 6. Work package D — the Borel growth lemma (T2)

**✅ DONE (2026-07-07).** Implemented in `VD/LLD/BorelGrowth.lean`; compiles lint-clean, ~120
lines. The proof deviates from the Vitali recommendation below: it slices the bad set `E` into
dyadic pieces `Eₙ = {r ∈ E | 2ⁿ · S a ≤ S r < 2ⁿ⁺¹ · S a}`. Any two points `x ≤ y` of `Eₙ`
satisfy `y − x < (S x)⁻¹ ≤ 2⁻ⁿ` (else monotonicity forces `S y ≥ S (x + (S x)⁻¹) > 2 · S x ≥
2ⁿ⁺¹ · S a > S y`), so `diam Eₙ ≤ 2⁻ⁿ` and `volume E ≤ Σ 2⁻ⁿ = 2 < ∞` by outer-measure
subadditivity (`measure_iUnion_le` + `Real.volume_le_diam`) — no covering lemma, no recursion,
and no measurability argument at all.

*Pure measure theory / real analysis; fully parallel to A–C. Suggested target file
`Mathlib/MeasureTheory/Function/BorelGrowth.lean` (maintainers may prefer another home).*

Statement as in T2 above. Recommended proof: **Vitali covering, no recursion.**

Let `E := {r ≥ a | S (r + (S r)⁻¹) > 2 * S r}` and `g := Real.log ∘ S` (monotone).
For `r ∈ E` set `δ r := (S r)⁻¹ ∈ (0, 1]`; then `g (r + δ r) − g r > log 2`.
- Apply `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall` to the balls
  `closedBall (r + δ r / 2) (δ r / 2)`, `r ∈ E`: get a disjoint countable subfamily
  whose 5-fold enlargements cover `E`.
- Disjointness + monotonicity of `g`: ordering the chosen centers `r₁ < r₂ < …`,
  `g (r_{i+1}) ≥ g (r_i + δ r_i) > g (r_i) + log 2`, so `g (r_i) ≥ g (r_1) + (i−1) log 2`,
  i.e. `δ r_i = exp (−g r_i) ≤ 2^{−(i−1)} / S r₁ ≤ 2^{−(i−1)}`.
- Hence `volume E ≤ 5 · Σ δ r_i ≤ 10 < ∞`, giving `Eᶜ ∈ volume.cofinite` and the claim.

Care points: measurability of `E` (S monotone ⇒ measurable; alternatively use outer
measure — `volume E < ∞` does not need measurability if stated via `≤` on the outer
measure of a covering union), and the countable-ordering argument
(disjoint positive-length intervals in `ℝ` are countable and order-isomorphic to a
subset of `ℕ`). Fallback proof: classical greedy recursion (Hayman Lemma 2.4) —
works, but the inductive construction with `sInf` is fiddlier in Lean than Vitali.

Estimated size: 250–350 lines. Difficulty: medium; zero dependencies on A–C.

---

## 7. Work package E — assembly (T3) and corollaries

**✅ DONE (2026-07-08).** Implemented in `VD/LLD/LogDerivLemma.lean` (~240 lines); compiles
lint-clean. `ValueDistribution.isBigO_proximity_logDeriv` (T3) and
`ValueDistribution.isBigO_proximity_logDeriv_of_isBigO_rpow` (finite-order corollary, via
`R := 2r`, no Borel lemma) are stated exactly as planned; the sanity check for `f = Complex.exp`
is included as an `example` (`Complex.logDeriv_exp` already exists in Mathlib). Deviations from
the sketch below: `S := fun r ↦ max 1 (characteristic f ⊤ r)` (arguments swapped, matching
`posLog_eq_log_max_one`); constants are absorbed using `1 ≤ log r` for `r ≥ e`, giving the
explicit big-O constants `c·(3 + 2 log 2)` (T3) and `c·(log⁺ C + ρ⁺ log 2 + log 2 + 2 + ρ⁺)`
(corollary, `ρ⁺ := max ρ 0`); the convenience unfolding with explicit exceptional sets was not
added — `volume.cofinite ⊓ atTop` membership is already idiomatic.

With `S := fun r ↦ max (characteristic f ⊤ r) 1` (monotone on `Ici 1` by
`characteristic_monotoneOn`, `≥ 1`), apply T1 with `R := r + (S r)⁻¹`:

- `log⁺ (R − r)⁻¹ = log (S r) = log⁺ (characteristic f ⊤ r)`;
- `log R ≤ log (r + 1) ≤ log r + log 2` for `r ≥ 1`;
- on the Borel-good set, `characteristic f ⊤ R ≤ S R ≤ 2 * S r`, so
  `log⁺ (characteristic f ⊤ R) ≤ log⁺ (characteristic f ⊤ r) + log 2`;
- absorb constants using `1 ≤ log r` for `r ≥ e` (eventually along `atTop ≥ the inf filter`).

This yields T3 in a ~100-line proof. Corollaries to include in the same file:

```lean
-- no exceptional set for finite order (R := 2r in T1, Borel lemma not needed):
isBigO_proximity_logDeriv_of_isBigO_rpow  -- see §1

-- convenience unfolding for users who prefer explicit exceptional sets:
-- ∃ E, volume E < ⊤ ∧ ∀ᶠ r in atTop, r ∉ E → proximity … r ≤ c * (…)
```

Optional sanity lemmas (cheap, good for the PR description): for `f = Complex.exp`,
`logDeriv f = 1` and the proximity term vanishes; for polynomials, T3 holds with
bounded LHS.

---

## 8. File layout and PR sequencing

All LLD work lives in the self-contained directory `VD/LLD/` (this plan included),
one local file per future Mathlib target:

| # | Local file (`VD/LLD/`) | Mathlib target | Contents | Depends on |
|---|---|---|---|---|
| 1 | `MeromorphicLogDeriv.lean` ✅ | `Analysis/Meromorphic/LogDeriv.lean` | package A (done) | — |
| 2 | `PosLog.lean` ✅ | `Analysis/SpecialFunctions/Log/PosLog.lean` (extend) | `posLog_rpow`, `abs_log_…` (done) | — |
| 3 | `BorelGrowth.lean` ✅ | `MeasureTheory/Function/BorelGrowth.lean` | package D (T2, done) | — |
| 4 | `CauchyIntegralDeriv.lean` ✅ | `MeasureTheory/Integral/CircleIntegral.lean` (extend) | B1–B3 (done) | — |
| 5 | `PoissonSchwarzDeriv.lean` ✅ | `Analysis/Complex/Poisson.lean` (extend) | B4, B5 (done) | 4, **Poisson–Jensen chain** |
| 6 | `PoissonJensenDeriv.lean` ✅ | `Analysis/Complex/PoissonJensenDeriv.lean` | B6 (done) | 1, 5 |
| 7 | `CircleAverageEstimates.lean` ✅ | `MeasureTheory/Integral/CircleAverage.lean` (extend) + `PosLog…` | C1, C2 (done) | — |
| 8 | `CountingEstimate.lean` ✅ | `…/ValueDistribution/LogCounting/Basic.lean` (extend) | C3 (done) | — |
| 9 | `LogDerivTwoRadius.lean` ✅ | `…/ValueDistribution/LogDerivLemma.lean` (part 1) | C4 (T1, done) | 1, 6, 7, 8 |
| 10 | `LogDerivLemma.lean` ✅ | `…/ValueDistribution/LogDerivLemma.lean` (part 2) | E (T3 + corollaries, done) | 3, 9 |

- Items 1–4, 7, 8 are **fully parallel** and independently PR-able today.
- The **critical path** is the pending Poisson–Jensen upstream chain
  (`BlaschkeDecomp2` [submitted] → `BlaschkeDecomp3`, `PoissonJensen` [pending])
  → 5 → 6 → 9 → 10.
- Every PR stays under ~400 lines. New Mathlib files must use the module system
  (`module` / `public import` / `@[expose] public section`) as in the current
  ValueDistribution files; the local VD copies can stay in classic mode until upstreaming.
- Doc-string style: follow `FirstMainTheorem.lean` (quantitative lemma with explicit
  constant + qualitative `isBigO` corollary; references to [MR886677] and
  Noguchi–Winkelmann [MR3156076]).

Total new code estimate: ≈ 2000–2400 lines of Lean.

## 9. Risks and fallbacks

1. **B6 bookkeeping** (finsums over divisors, codiscrete filters) is the largest single
   proof. Mitigation: it is structurally identical to the existing `poissonJensen₀`
   proof; reuse its helper lemmas (`continuousOn_herglotzRieszKernel_sphere`,
   integrability lemmas) — several already live in `VD/MathlibPending/PoissonJensen.lean`
   and should be upstreamed with it.
2. **Boundary zeros/poles** (divisor on the sphere). Primary plan: handled by the B4
   special case `h = (· − u)`. Fallback: state B6 only for radii whose sphere carries
   no divisor points (only finitely many bad radii in `[r, R]`), and pick a good `ρ`
   in C4 using monotonicity of `characteristic` — mathematically harmless, slightly
   uglier statement.
3. **Jensen inequality hypotheses** (`ConcaveOn.le_map_average` wants a closed set,
   a.e. membership, two integrabilities). Mitigation: C1 is designed as a standalone
   lemma so the fiddling happens once; apply it to the explicit *bound* function
   (whose integrability is termwise), never to `‖logDeriv f‖^{1/2}` itself.
4. **Borel lemma measurability.** If `E`'s measurability is annoying, phrase the
   conclusion via a measurable superset or outer measure; `volume.cofinite`
   membership only needs *some* finite-measure superset of the bad set.
5. **Upstream latency** of the Poisson–Jensen chain. All other packages (1–4, 7, 8, D)
   are independent; schedule them first while reviews run.

## 10. Milestones

1. **M1** (independent, parallel): packages A, D, B1–B3, C1–C3 compile in VD. Each is
   individually PR-able.
2. **M2**: B4–B6 — differentiated Poisson–Jensen proved (sanity check: `f = id`, `R = 1`
   as above; also `f` a finite Blaschke product where the kernel term vanishes).
3. **M3**: T1 (two-radius estimate) + the finite-order corollary
   (`proximity (logDeriv f) ⊤ =O[atTop] log` — already a citable result).
4. **M4**: T3 assembled; sanity corollaries; upstream PRs for 6, 9, 10.
5. **Post-LLD** (out of scope here, prepares SMT): divisor/`logCounting` bounds for
   `logDeriv f` (simple poles ⇒ `N(r, f′/f) ≤ N̄(r,f,0) + N̄(r,f,∞)`), and
   `m(r, f′/(f − a))` for several targets `a` via T3 + FMT.
