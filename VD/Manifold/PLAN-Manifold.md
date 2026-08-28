# Plan: Nevanlinna theory for holomorphic maps `ℂ → M`

Working plan for extending the Value Distribution library in
`Mathlib/Analysis/Complex/ValueDistribution/` from meromorphic functions `ℂ → ℂ` to holomorphic
maps `f : ℂ → M` into a complex manifold `M` carrying a holomorphic line bundle `L`, a continuous
Hermitian metric `‖·‖` on `L`, and a holomorphic section `σ` with `σ ∘ f ≢ 0`. Prepared
2026-08-28 against the Mathlib checkout in `.lake` (commit `661ab0bdd381…`, toolchain
v4.34.0-rc2). Companion to `VD/LLD/PLAN-LogarithmicDerivative.md` and
`VD/SMT/PLAN-SecondMainTheorem.md`, whose results are consumed unchanged.

The mathematical target is the framework of Noguchi–Winkelmann [MR3156076] §2.7 as used in
`~/Mathe/orbiAlb/orbiAlb3` §4 (Kebekus–Rousseau, *Entire curves in 𝒞-pairs with large
irregularity*) and `~/Mathe/orbiBO` §3 / App. A.

---

## 1. Goal

**Classical statements** (source `ℂ`; the papers work over a finite cover `ρ : V → ℂ`, see
Milestone 4). For `f : ℂ → M` holomorphic, `(L, ‖·‖)` a Hermitian line bundle, `σ ∈ H⁰(M, L)`
with `σ ∘ f ≢ 0`, and `D := div σ`:

```
N(r, f, σ)   = ∫₀ʳ (n(t) − n(0)) dt/t + n(0)·log r,   n(t) = #{ |z| ≤ t : σ(f z) = 0 } with mult.
m(r, f, σ)   = (1/2π) ∫₀^{2π} log ( 1 / ‖σ(f(r e^{iθ}))‖ ) dθ            (plain log, not log⁺)
T(r, f, σ)   = m(r, f, σ) + N(r, f, σ)
FMT:  T(•, f, σ₁) − T(•, f, σ₂) = const   for σ₁, σ₂ ∈ H⁰(M, L)      (so T depends on L up to O(1))
      T(•, f, σ) with respect to ‖·‖₁ and ‖·‖₂ differ by O(1)          (M compact)
      m(•, f, σ) ≥ −log sup ‖σ‖                                          (M compact)
      T(•, φ ∘ f) ≤ T(•, f, τ) + O(1)  for φ = σ/τ meromorphic on M      (height functoriality)
```

Comparison with the existing theory: for `f : ℂ → ℂ` meromorphic, `F : ℂ → ℙ¹` its extension,
`H = (𝒪(1), Fubini–Study)`, `θ_a ∈ H⁰(𝒪(1))` the section vanishing at `a ∈ ℂ ∪ {∞}`
(`|θ_∞(z)|² = 1/(1+|z|²)`, `|θ_a(z)|² = |z−a|²/(1+|z|²)`):

```
N(r, F, θ_a)  =  logCounting f a r                                     (exact)
|m(r, F, θ_∞) − proximity f ⊤ r|  ≤  ½ log 2
|m(r, F, θ_a) − proximity f a r|  ≤  ½ log 2 + log⁺|a| + log 2
```

References:

- Noguchi–Winkelmann, *Nevanlinna theory in several complex variables and Diophantine
  approximation* [MR3156076], §2.3, §2.5 (heights vs. coordinates: Thm 2.5.13, 2.5.18), §2.7
  (FMT: Thm 2.7.4);
- Noguchi, *On the value distribution of meromorphic mappings of covering spaces over ℂ^m into
  algebraic varieties* [MR780664], Lem. 1.6 (LLD for log forms), p. 298 (`log⁺` proximity);
- Yamanoi, *Kobayashi hyperbolicity and higher-dimensional Nevanlinna theory* [MR3331401],
  §3, proof of Lem. 3.1 (metric independence);
- Lang, *Introduction to Complex Hyperbolic Spaces* [MR886677], Ch. VI (Weil functions,
  counting-function convention already used in Mathlib);
- Kebekus–Rousseau, orbiAlb3 §4: Reminders 4.2/4.3, Lemmas 4.5–4.7, Thm 4.8, Not. 4.10, Thm 4.11;
  orbiBO §3, Remark A-1, Lemma A-2, Claim 7-17.

**Formal targets (Milestone 1).**

```lean
-- New Mathlib-level notion: continuous fibre norm on a vector bundle.
class Bundle.IsContinuousNormBundle (F : Type*) (E : B → Type*) … : Prop where
  continuous_norm : Continuous (fun p : TotalSpace F E ↦ ‖p.2‖)

-- Divisor of σ ∘ f on ℂ, and the three Nevanlinna functions.
noncomputable def ValueDistribution.sectionDivisor (σ : Π x, L x) (f : ℂ → M) :
    Function.locallyFinsupp ℂ ℤ
noncomputable def ValueDistribution.logCountingSection (f : ℂ → M) (σ : Π x, L x) : ℝ → ℝ :=
  (sectionDivisor σ f).logCounting
noncomputable def ValueDistribution.proximitySection (f : ℂ → M) (σ : Π x, L x) : ℝ → ℝ :=
  circleAverage (fun z ↦ Real.log ‖σ (f z)‖⁻¹) 0
noncomputable def ValueDistribution.characteristicSection (f : ℂ → M) (σ : Π x, L x) : ℝ → ℝ :=
  proximitySection f σ + logCountingSection f σ

-- (M1) First Main Theorem, exact form: independence of the section.
theorem ValueDistribution.characteristicSection_sub_characteristicSection
    (hf : ContMDiff 𝓘(ℂ) I ω f) (hσ : ContMDiff I (I.prod 𝓘(ℂ, ℂ)) ω (T% σ))
    (hτ : ContMDiff I (I.prod 𝓘(ℂ, ℂ)) ω (T% τ)) (hσf : ∃ z, σ (f z) ≠ 0) (hτf : ∃ z, τ (f z) ≠ 0)
    (hR : R ≠ 0) :
    characteristicSection f σ R - characteristicSection f τ R
      = - Real.log ‖meromorphicTrailingCoeffAt (Bundle.sectionRatio σ τ ∘ f) 0‖

-- (M2) Height functoriality: the classical characteristic of a section ratio.
theorem ValueDistribution.characteristic_sectionRatio_le [CompactSpace M] … :
    ∃ c, ∀ r, characteristic (Bundle.sectionRatio σ τ ∘ f) ⊤ r ≤ characteristicSection f τ r + c

-- (M3) ℙ¹ = OnePoint ℂ as complex manifold, 𝒪(1) with Fubini–Study norm, sections θ_a,
--      Meromorphic.toRiemannSphere : (ℂ → ℂ) → (ℂ → OnePoint ℂ).

-- (M4) Comparison with the classical theory.
theorem ValueDistribution.logCountingSection_theta_eq_logCounting (hf : Meromorphic f) (a) :
    logCountingSection (Meromorphic.toRiemannSphere f) (RiemannSphere.theta a) = logCounting f a
theorem ValueDistribution.abs_proximitySection_theta_sub_proximity_le (hf : Meromorphic f) (a) (r) :
    |proximitySection (toRiemannSphere f) (theta a) r - proximity f a r|
      ≤ Real.log 2 / 2 + log⁺ ‖a‖ + Real.log 2          -- constant `log 2 / 2` for a = ∞
```

### Design decisions (and why)

1. **Height is section-based, `T := m + N`.** The curvature (Ahlfors–Shimizu) definition
   `∫₀ʳ (∫_{|z|<t} f*c₁(L,h)) dt/t` needs `dd^c`, a Green–Jensen formula and smooth Hermitian
   metrics — none of which exist in Mathlib. With the section-based definition the FMT is an
   *identity* via Jensen (`Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const`),
   and the curvature version becomes a theorem later (Milestone 3).

2. **Proximity uses plain `log`, not `log⁺`.** (i) `log‖σ∘f‖ − log‖τ∘f‖ = log|(σ/τ)∘f|` exactly,
   so M1 is exact and `m` is exactly additive under products of sections; (ii) a change of metric
   by a factor `ρ` shifts `m` by exactly `circleAverage (log ρ∘f)`, and on compact `M` one may
   scale so that `‖σ‖ ≤ 1`, where `log = log⁺` anyway; (iii) `−log‖σ‖` is the Weil-function /
   `dd^c` convention needed for Milestone 3; (iv) Mathlib's `log⁺‖f‖` *is* `log(1/‖θ_∞∘F‖)` for
   the continuous metric `|θ_∞|² = 1/max(1,|z|²)` on `𝒪(1)`, so `log⁺` is a special case, not a
   rival convention. Price: `m ≥ 0` only up to `−log sup‖σ‖`, needing `[CompactSpace M]`.

3. **Agreement with `ValueDistribution.proximity/characteristic` is demanded only up to explicit
   constants; `logCounting` agrees exactly.** No single metric on `𝒪(1)` reproduces `log⁺` for
   all values `a` simultaneously (Mathlib's own FMT part 2 carries the shift `log⁺‖a‖ + log 2`).
   The existing definitions are not touched and not generalized.

4. **Mathlib's `VectorBundle` API, plus one new Prop-class `IsContinuousNormBundle`.** Fibre norms
   are instances `[∀ x, NormedAddCommGroup (L x)] [∀ x, NormedSpace ℂ (L x)]`; the class only asks
   the norm to be continuous on the total space (modelled on `IsContinuousRiemannianBundle` in
   `Mathlib/Topology/VectorBundle/Riemannian.lean`). No sesquilinear/`C^n` Hermitian structure is
   needed before Milestone 3. Holomorphic = `ContMDiff … ω` (`ω = ⊤ : WithTop ℕ∞`);
   holomorphic bundle = `ContMDiffVectorBundle ω ℂ L I`.

5. **Mathlib's conventions throughout**: radii `r ∈ ℝ` (junk for `r ≤ 0`), `1/(2π)` via
   `circleAverage`, Lang's `D(0)·log r` term in `logCounting`. The papers' `∫₁ʳ … ds/s` differs by
   a constant; record this in one lemma, never adopt it.

6. **Non-degeneracy as `∃ z, σ (f z) ≠ 0`.** Since ℂ is connected and `σ ∘ f` is holomorphic in
   local coordinates, this makes the zero set discrete (identity theorem); it is the manifold
   analogue of `f ≢ 0`.

7. **Statements about trivializations are made for an arbitrary `e` with `he : x ∈ e.baseSet`**,
   then specialized to `trivializationAt ℂ L x` — this is the standard way to keep the
   dependent-type overhead of `VectorBundle` under control.

8. **Source is ℂ.** The papers' finite branched covers `ρ : V → ℂ` are recorded as Milestone 4;
   the definitions here are chosen so that the cover case reduces to push-forwards (fibre sums).

9. **Scope honesty.** FMT and height functoriality generalize fully; the LLD generalizes in
   Noguchi's log-form version (Milestone 2, with the algebraic-geometric input as explicit
   hypotheses); the SMT / defect relation for general `M` are Griffiths' *conjecture* and exist
   only for `ℙ¹` (already in `VD/SMT/`) and `ℙⁿ` with hyperplanes (Cartan; separate project).

---

## 2. Inventory

### Already available (verified in the 2026-08-28 checkout)

Value distribution (Mathlib): `Function.locallyFinsuppWithin` (needs only `[TopologicalSpace X]`),
`Function.locallyFinsuppWithin.logCounting` and `logCounting_divisor_eq_circleAverage_sub_const`,
`MeromorphicOn.divisor`, `MeromorphicOn.circleAverage_log_norm` (Jensen),
`MeromorphicOn.circleIntegrable_log_norm`, `circleAverage` API (`circleAverage_add/sub/mono`,
`circleAverage_congr_codiscreteWithin`), `Real.posLog` API (`posLog_le_log_one_add`,
`log_one_add_le_posLog`, `posLog_add`), `ValueDistribution.{logCounting,proximity,characteristic}`,
FMT parts 1/2, Cartan's formula; project: LLD (`VD/LLD/`), SMT/defects/Picard (`VD/SMT/`),
`characteristic_isBigO_one_iff_constant` (`VD/MathlibPending/`).

Meromorphic functions: `MeromorphicNFAt`, `toMeromorphicNFOn`, `meromorphicNFAt_iff_analyticAt_or`,
`MeromorphicNFAt.inv`, `meromorphicOrderAt`, `analyticOrderAt`, `analyticOrderAt_mul`,
`meromorphicTrailingCoeffAt`, `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`,
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`.

Manifolds: `IsManifold I ω M`, `isManifold_of_contDiffOn`, `ContMDiff/ContMDiffAt`,
`contMDiff_iff_contDiff`, `contDiff_omega_iff_analyticOnNhd`, `analyticOnNhd_univ_iff_differentiable`;
`Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean` as the only complex 1-manifold instance
(template for `contMDiffAt_iff` glue); `Mathlib/Geometry/Manifold/Complex.lean` (max modulus).

Bundles: `FiberBundle`, `VectorBundle`, `Trivialization.{linearEquivAt,symmL,continuousLinearEquivAt}`,
`VectorBundleCore` + `VectorBundleCore.IsContMDiff`, `VectorPrebundle` + `VectorPrebundle.IsContMDiff`,
`ContMDiffVectorBundle`, `contMDiffAt_section`, `contMDiffAt_section_iff`,
`Trivialization.contMDiffAt_symmL`, `Bundle.Pullback`/`ContMDiffVectorBundle.pullback`,
`Bundle.Trivial`, hom-bundles `fun x ↦ E₁ x →L[ℂ] E₂ x` (`Bundle.ContinuousLinearMap.*`),
`IsContinuousRiemannianBundle` / `RiemannianMetric` / `ContinuousRiemannianMetric` (real, template).

Riemann sphere: `OnePoint ℂ` with topology, `CompactSpace`, `T4Space`, `ConnectedSpace`,
`isOpenEmbedding_coe`, `continuousAt_infty`, `nhds_infty_eq`; `OnePoint.equivProjectivization`,
`MulAction (GL (Fin 2) ℂ) (OnePoint ℂ)` (`Topology/Compactification/OnePoint/ProjectiveLine.lean`).

### Missing (= the actual work, work packages WP0–WP9)

- Flat-case glue `ContMDiff … ω ↔ Differentiable ℂ` for `ℂ → ℂ` (WP0).
- Continuous fibre norms on bundles, frames, bounds on compact base (WP1).
- Local coordinates of sections, section ratios, analyticity along `f` (WP2).
- Divisor of `σ ∘ f` on ℂ (WP3); the Nevanlinna functions (WP4); FMT, metric independence,
  functoriality, growth (WP5).
- Complex-manifold structure on `OnePoint ℂ` (WP6); `Meromorphic.toRiemannSphere` (WP7);
  `𝒪(1)` with Fubini–Study norm and `θ_a` (WP8); comparison theorems (WP9).
- Not in Mathlib and not needed for Milestone 1: tensor/dual line bundles, `𝒪(k)`, ℙⁿ, smooth
  Hermitian metrics, Chern forms, Green/Stokes on disks, Riemann surfaces, finite covers.

---

## 3. Work package WP0 — flat glue ⬜

File `VD/Manifold/HolomorphicFlat.lean`.

```lean
theorem contMDiff_omega_iff_differentiable {f : ℂ → ℂ} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f ↔ Differentiable ℂ f
theorem ContMDiffAt.analyticAt_of_flat {f : ℂ → ℂ} {z : ℂ} (h : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f z) :
    AnalyticAt ℂ f z
```

Proof: `contMDiff_iff_contDiff`, `contDiff_omega_iff_analyticOnNhd`,
`analyticOnNhd_univ_iff_differentiable`, `ContDiffAt.analyticAt`.

## 4. Work package WP1 — continuous norm bundles ⬜

File `VD/Manifold/Bundle/ContinuousNorm.lean`. Variables as in Mathlib's Riemannian files,
fibre `F`, bundle `E : B → Type*`, `[∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]`,
`[FiberBundle F E] [VectorBundle 𝕜 F E]`.

```lean
class Bundle.IsContinuousNormBundle (F E) : Prop where
  continuous_norm : Continuous (fun p : TotalSpace F E ↦ ‖p.2‖)
instance : IsContinuousNormBundle F (Bundle.Trivial B F)
instance [IsContinuousRiemannianBundle F E] : IsContinuousNormBundle F E
theorem Continuous.norm_bundle {s : Π x, E x} (hs : Continuous (fun x ↦ TotalSpace.mk' F x (s x))) :
    Continuous (fun x ↦ ‖s x‖)
theorem Trivialization.continuousOn_norm_frame (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    ContinuousOn (fun x ↦ ‖e.symmL 𝕜 x 1‖) e.baseSet         -- line bundles: F = 𝕜
theorem Trivialization.norm_frame_pos (he : x ∈ e.baseSet) : 0 < ‖e.symmL 𝕜 x 1‖
theorem exists_norm_le_of_compactSpace [CompactSpace B] (hs : Continuous (T% s)) :
    ∃ C, ∀ x, ‖s x‖ ≤ C
```

## 5. Work package WP2 — local coordinates and section ratios ⬜

File `VD/Manifold/Bundle/LocalCoord.lean`. Line bundle `L : M → Type*` with fibre `ℂ`.

```lean
def Bundle.localCoord (e : Trivialization ℂ (π ℂ L)) (σ : Π x, L x) (x : M) : ℂ := (e ⟨x, σ x⟩).2
theorem Bundle.norm_eq_localCoord_mul_norm_frame (he : x ∈ e.baseSet) :
    ‖σ x‖ = ‖localCoord e σ x‖ * ‖e.symmL ℂ x 1‖
theorem ContMDiffAt.analyticAt_localCoord_comp {f : ℂ → M} {z : ℂ}
    (hf : ContMDiffAt 𝓘(ℂ) I ω f z) (hσ : ContMDiffAt I (I.prod 𝓘(ℂ, ℂ)) ω (T% σ) (f z))
    (he : f z ∈ e.baseSet) : AnalyticAt ℂ (localCoord e σ ∘ f) z
def Bundle.sectionRatio (σ τ : Π x, L x) : M → ℂ :=
  fun x ↦ localCoord (trivializationAt ℂ L x) σ x / localCoord (trivializationAt ℂ L x) τ x
theorem Bundle.sectionRatio_eq_div_localCoord (he : x ∈ e.baseSet) :
    sectionRatio σ τ x = localCoord e σ x / localCoord e τ x
theorem Bundle.norm_eq_norm_sectionRatio_mul (hτ : τ x ≠ 0) : ‖σ x‖ = ‖sectionRatio σ τ x‖ * ‖τ x‖
theorem MeromorphicAt.sectionRatio_comp … : MeromorphicAt (sectionRatio σ τ ∘ f) z
theorem Meromorphic.sectionRatio_comp … : Meromorphic (sectionRatio σ τ ∘ f)
```

Proof notes: `contMDiffAt_section` (Mathlib, `Geometry/Manifold/VectorBundle/Basic.lean`)
converts smoothness of `T% σ` into smoothness of `localCoord (trivializationAt …) σ`; composition
with `hf`, then WP0. Trivialization independence via `Trivialization.coordChangeL`
(non-vanishing analytic scalar). The ratio is meromorphic as a quotient of analytic functions
(`AnalyticAt.meromorphicAt`, `MeromorphicAt.div`), also when the denominator vanishes
identically near `z` (then it is meromorphic with order `⊤`).

## 6. Work package WP3 — the divisor of `σ ∘ f` ⬜

File `VD/Manifold/SectionDivisor.lean`.

```lean
noncomputable def ValueDistribution.sectionOrderAt (σ : Π x, L x) (f : ℂ → M) (z : ℂ) : ℕ∞ :=
  analyticOrderAt (Bundle.localCoord (trivializationAt ℂ L (f z)) σ ∘ f) z
theorem sectionOrderAt_eq_analyticOrderAt_localCoord (he : f z ∈ e.baseSet) :
    sectionOrderAt σ f z = analyticOrderAt (localCoord e σ ∘ f) z
noncomputable def ValueDistribution.sectionDivisor (σ) (f) : Function.locallyFinsupp ℂ ℤ
  -- value `(sectionOrderAt σ f z).toNat` if `hf`, `hσ`, `hσf` hold, else `0` (junk)
theorem sectionDivisor_apply … : sectionDivisor σ f z = (sectionOrderAt σ f z).toNat
theorem sectionDivisor_nonneg : 0 ≤ sectionDivisor σ f
theorem sectionDivisor_sub_eq_divisor_sectionRatio … :
    sectionDivisor σ f - sectionDivisor τ f = MeromorphicOn.divisor (sectionRatio σ τ ∘ f) univ
```

Local finiteness: `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` plus the identity
theorem on the connected set `univ` (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`)
plus `hσf`. Follow `MeromorphicOn.divisor` (`Mathlib/Analysis/Meromorphic/Divisor.lean`) for the
junk-value pattern.

## 7. Work package WP4 — proximity and counting ⬜

Files `VD/Manifold/Proximity.lean`, `VD/Manifold/Counting.lean`.

```lean
noncomputable def proximitySection (f : ℂ → M) (σ : Π x, L x) : ℝ → ℝ :=
  circleAverage (fun z ↦ Real.log ‖σ (f z)‖⁻¹) 0
theorem circleIntegrable_log_norm_section … (r : ℝ) :
    CircleIntegrable (fun z ↦ Real.log ‖σ (f z)‖) 0 r
theorem proximitySection_sub_proximitySection … (hR : R ≠ 0) :
    proximitySection f σ R - proximitySection f τ R
      = - circleAverage (fun z ↦ Real.log ‖sectionRatio σ τ (f z)‖) 0 R
theorem neg_log_le_proximitySection [CompactSpace M] … (hC : ∀ x, ‖σ x‖ ≤ C) (hR : R ≠ 0) :
    - Real.log C ≤ proximitySection f σ R
noncomputable def logCountingSection (f : ℂ → M) (σ : Π x, L x) : ℝ → ℝ :=
  (sectionDivisor σ f).logCounting
theorem logCountingSection_nonneg (hr : 1 ≤ r) …, logCountingSection_monotoneOn …
```

Integrability: locally on the circle, `log‖σ∘f‖ = log|localCoord e σ ∘ f| + log‖frame ∘ f‖`
(WP2), first summand by `MeromorphicOn.circleIntegrable_log_norm`, second continuous; patch via
`CircleIntegrable ↔ IntervalIntegrable (f ∘ circleMap …)` and
`LocallyIntegrableOn.integrableOn_isCompact`. Keep the patching lemma general ("locally
`log|analytic| + continuous` ⇒ circle integrable") for reuse in Milestone 3.

## 8. Work package WP5 — characteristic, FMT, functoriality ⬜

File `VD/Manifold/Characteristic.lean`.

```lean
noncomputable def characteristicSection (f) (σ) : ℝ → ℝ := proximitySection f σ + logCountingSection f σ
-- M1 (exact FMT)
theorem characteristicSection_sub_characteristicSection … (hR : R ≠ 0) :
    characteristicSection f σ R - characteristicSection f τ R
      = - Real.log ‖meromorphicTrailingCoeffAt (sectionRatio σ τ ∘ f) 0‖
theorem isBigO_characteristicSection_sub_characteristicSection … :
    (characteristicSection f σ - characteristicSection f τ) =O[atTop] (1 : ℝ → ℝ)
-- metric independence (Lemma 4.6 analogue), stated through the ratio ρ of two fibre norms
theorem abs_circleAverage_log_comp_le [CompactSpace M] {ρ : M → ℝ} (hρ : Continuous ρ)
    (hρ₀ : ∀ x, 0 < ρ x) : ∃ c, ∀ R, |circleAverage (fun z ↦ Real.log (ρ (f z))) 0 R| ≤ c
-- M2 (height functoriality; orbiBO Lem. A-2, Claim 7-17)
theorem characteristic_sectionRatio_le [CompactSpace M] … :
    ∃ c, ∀ r, characteristic (sectionRatio σ τ ∘ f) ⊤ r ≤ characteristicSection f τ r + c
-- growth (Lemma 4.7 analogue, "ample" replaced by a non-constant section ratio)
theorem log_le_characteristicSection_add_const … (h : ¬ EventuallyConst (sectionRatio σ τ ∘ f) (codiscrete ℂ)) :
    ∃ c, ∀ r ≥ 1, Real.log r ≤ characteristicSection f τ r + c
```

Proof of M1: WP4 difference formula + WP3 divisor formula +
`logCounting_divisor_eq_circleAverage_sub_const`. Proof of M2: `N(g, ∞) ≤ N_τ` from the divisor
formula; `log⁺|g| ≤ log⁺‖σ∘f‖ + log⁺(1/‖τ∘f‖) ≤ 2 log⁺C + log(1/‖τ∘f‖)`.

## 9. Work package WP6 — the Riemann sphere as a complex manifold ⬜

File `VD/Manifold/RiemannSphere/Manifold.lean`.

```lean
instance : ChartedSpace ℂ (OnePoint ℂ)          -- charts: `some` on {∞}ᶜ, `p ↦ p⁻¹` on {0}ᶜ
instance : IsManifold 𝓘(ℂ) ω (OnePoint ℂ)         -- transition z ↦ z⁻¹ analytic on ℂ ∖ {0}
theorem OnePoint.contMDiff_coe : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((↑) : ℂ → OnePoint ℂ)
theorem OnePoint.contMDiffAt_iff … -- glue in the style of UpperHalfPlane.contMDiffAt_iff
```

Continuity of inversion at `∞`: `OnePoint.continuousAt_infty`, `nhds_infty_eq`, tendsto of
`z⁻¹` along `cocompact ℂ`. `isManifold_of_contDiffOn` with `contDiffOn_omega_iff_analyticOn`.

## 10. Work package WP7 — meromorphic functions as maps to ℙ¹ ⬜

File `VD/Manifold/RiemannSphere/OfMeromorphic.lean`.

```lean
noncomputable def Meromorphic.toRiemannSphere (f : ℂ → ℂ) (z : ℂ) : OnePoint ℂ :=
  if 0 ≤ meromorphicOrderAt f z then ↑(toMeromorphicNFOn f univ z) else ∞
theorem Meromorphic.contMDiff_toRiemannSphere (hf : Meromorphic f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toRiemannSphere f)
theorem Meromorphic.toRiemannSphere_eq_coe_codiscrete (hf : Meromorphic f) :
    toRiemannSphere f =ᶠ[codiscrete ℂ] fun z ↦ ↑(f z)
-- optional converse: holomorphic F : ℂ → ℙ¹ with F ≢ ∞ is toRiemannSphere of a meromorphic f
```

Non-poles: `toMeromorphicNFOn` is analytic where the order is `≥ 0`
(`meromorphicNFAt_iff_analyticAt_or`); poles: second chart and `MeromorphicNFAt.inv`.

## 11. Work package WP8 — `𝒪(1)`, Fubini–Study norm, sections `θ_a` ⬜

File `VD/Manifold/RiemannSphere/Hyperplane.lean`. The most laborious package; WP0–WP5 must not
depend on it.

Recommended construction (norms come for free, no topology diamond):
```lean
def RiemannSphere.line : OnePoint ℂ → Submodule ℂ (EuclideanSpace ℂ (Fin 2))
  -- some z ↦ ℂ ∙ ![z, 1],  ∞ ↦ ℂ ∙ ![1, 0]
abbrev RiemannSphere.hyperplaneBundle (p : OnePoint ℂ) := line p →L[ℂ] ℂ     -- 𝒪(1) = dual of 𝒪(−1)
-- FiberBundle/VectorBundle via VectorPrebundle with two pretrivializations
--   (evaluate at ![z, 1] over {∞}ᶜ, at ![1, z⁻¹] over {0}ᶜ; transition = multiplication by z),
-- ContMDiffVectorBundle ω via VectorPrebundle.IsContMDiff, IsContinuousNormBundle from the formula.
def RiemannSphere.theta (a : OnePoint ℂ) : Π p, hyperplaneBundle p   -- restriction of v ↦ a₁v₀ − a₀v₁
theorem norm_theta_some (a z : ℂ) : ‖theta a (some z)‖ = ‖z - a‖ / √(1 + ‖z‖ ^ 2)
theorem norm_theta_infty (z : ℂ) : ‖theta ∞ (some z)‖ = 1 / √(1 + ‖z‖ ^ 2)
theorem contMDiff_theta (a) : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ)) ω (T% theta a)
theorem sectionRatio_theta (a b) : sectionRatio (theta a) (theta b) = Möbius coordinate (z − a)/(z − b)
```
Fallback: `VectorBundleCore ℂ (OnePoint ℂ) ℂ Bool` with `coordChange = (z • ·)` and a hand-made
norm on `Z.Fiber` using `InnerProductSpace.Core.toNormedAddCommGroupOfTopology` (as in
`Mathlib/Topology/VectorBundle/Riemannian.lean`) to keep the topology definitionally equal.

## 12. Work package WP9 — comparison with the classical theory ⬜

File `VD/Manifold/Classical.lean`. Throughout `hf : Meromorphic f`, `F := toRiemannSphere f`.

```lean
theorem sectionDivisor_theta_infty : sectionDivisor (theta ∞) F = (divisor f univ)⁻
theorem sectionDivisor_theta_coe (a : ℂ) : sectionDivisor (theta a) F = (divisor (f · - a) univ)⁺
theorem logCountingSection_theta_eq_logCounting (a : WithTop ℂ) :
    logCountingSection F (theta a) = logCounting f a                        -- exact
theorem abs_proximitySection_theta_infty_sub_proximity_le (r) :
    |proximitySection F (theta ∞) r - proximity f ⊤ r| ≤ Real.log 2 / 2
theorem abs_proximitySection_theta_coe_sub_proximity_le (a : ℂ) (r) :
    |proximitySection F (theta a) r - proximity f a r| ≤ Real.log 2 / 2 + log⁺ ‖a‖ + Real.log 2
theorem abs_characteristicSection_theta_sub_characteristic_le … -- same constants
theorem isBigO_characteristicSection_theta_sub_characteristic … =O[atTop] (1 : ℝ → ℝ)
```

Ingredients: `norm_theta_*`, `toRiemannSphere_eq_coe_codiscrete` +
`circleAverage_congr_codiscreteWithin`, `0 ≤ ½ log(1+x²) − log⁺ x ≤ ½ log 2`
(`posLog_le_log_one_add`, `log_one_add_le_posLog`), `|log⁺|f| − log⁺|f−a|| ≤ log⁺|a| + log 2`
(`posLog_add`). Sanity example: M1 for `θ_0, θ_∞` recovers
`characteristic_sub_characteristic_inv_le` up to the explicit constants.

Remark (no code): with the continuous metric `|θ_∞|² = 1/max(1,|z|²)` the agreement with
`proximity f ⊤` is exact, and the curvature height for it is Cartan's formula
`characteristic_top_eq_circleAverage_add_circleAverage`.

---

## 13. File layout and PR sequencing

```
VD/Manifold/HolomorphicFlat.lean              WP0   → Mathlib: Geometry/Manifold/ContMDiff/NormedSpace.lean
VD/Manifold/Bundle/ContinuousNorm.lean        WP1   → Mathlib: Topology/VectorBundle/ContinuousNorm.lean (new)
VD/Manifold/Bundle/LocalCoord.lean            WP2   → Mathlib: Geometry/Manifold/VectorBundle/LocalCoord.lean (new)
VD/Manifold/SectionDivisor.lean               WP3   → Mathlib: Analysis/Complex/ValueDistribution/Manifold/SectionDivisor.lean
VD/Manifold/Proximity.lean, Counting.lean     WP4   → …/ValueDistribution/Manifold/{Proximity,Counting}.lean
VD/Manifold/Characteristic.lean               WP5   → …/ValueDistribution/Manifold/Characteristic.lean
VD/Manifold/RiemannSphere/Manifold.lean       WP6   → Mathlib: Analysis/Complex/RiemannSphere/Manifold.lean (new)
VD/Manifold/RiemannSphere/OfMeromorphic.lean  WP7   → Mathlib: Analysis/Complex/RiemannSphere/OfMeromorphic.lean
VD/Manifold/RiemannSphere/Hyperplane.lean     WP8   → Mathlib: Analysis/Complex/RiemannSphere/Hyperplane.lean
VD/Manifold/Classical.lean                    WP9   → …/ValueDistribution/Manifold/Classical.lean
```

Dependencies: WP0 → WP2 → WP3 → WP4 → WP5 (general theory, upstreamable on its own);
WP1 → WP2; WP6 → WP7, WP8 → WP9 (needs WP5 and WP7). Register each new file in `VD.lean`.
Never place files in `VD/MathlibPending/` before they are PR-ready.

---

## 14. Risks and fallbacks

1. **Dependent types in `VectorBundle`** (`trivializationAt ℂ L (f z)` varies with `z`). Always
   prove for arbitrary `e` with `he`, then specialize (design decision 7).
2. **Few `ω`-instances in Mathlib** (`IsManifold 𝓘(ℂ) ω`, `ContMDiffVectorBundle ω`). Expect to
   prove `IsContMDiff` for `𝒪(1)` by hand via `contDiffOn_omega_iff_analyticOn`.
3. **WP8 may stall.** Fallback is the `VectorBundleCore` route; and WP0–WP5 plus WP6–WP7 already
   give the general theory and the ℙ¹ manifold without `𝒪(1)`.
4. **Circle-integrability patching lemma** (WP4) is new analysis; keep it general.
5. **Section-vs-metric bookkeeping**: two fibre norms on the same `L` are two instances; state
   metric independence through the ratio function `ρ` (WP5) rather than with `@`-instances.

---

## 15. Milestones

- **Milestone 1** (this plan): WP0–WP9. Deliverables M1–M4 above.
- **Milestone 2 — LLD for log 1-forms** (orbiAlb3 Thm 4.11, Noguchi Lem. 1.6). ℂ-level core:
  for meromorphic `a_i, φ_i` and `ξ := ∑ a_i · logDeriv φ_i`,
  `proximity ξ ⊤ ≤ ∑ proximity a_i ⊤ + ∑ proximity (logDeriv φ_i) ⊤ + log n`, then
  `ValueDistribution.isBigO_proximity_logDeriv`. Manifold form: hypothesis
  `ξ = ∑ (sectionRatio α_i β_i ∘ f) · logDeriv (sectionRatio γ_i δ_i ∘ f)` (encodes
  `ω = ∑ a_i dlog φ_i` with rational `a_i, φ_i` — Mathlib has no "projective"/"ample"/`Ω¹(log D)`),
  conclusion `∀ ε > 0, ∀ᶠ r in volume.cofinite ⊓ atTop, proximity ξ ⊤ r ≤ ε * characteristicSection f σ r`
  via M2 and the growth lemma. Also heights of algebraic elements (orbiBO Prop. 3-8, Lem. A-3,
  Valiron) — pure ℂ-level.
- **Milestone 3 — curvature height (Ahlfors–Shimizu).** `∂∂̄ = ¼Δ` via
  `VD/LinearDiffOp/Wirtinger.lean`; Green–Jensen `circleAverage u 0 r − u 0 = ∫₀ʳ (2πt)⁻¹ (∫_{ball 0 t} Δu) dt`
  for `C²` functions (Mathlib only has the box divergence theorem), then with log singularities;
  smooth Hermitian metric class; `f*c₁ := −(2π)⁻¹ Δ log‖σ∘f‖` off the zeros (section-independent by
  `AnalyticAt.harmonicAt_log_norm`); `characteristicCurv f = characteristicSection f σ − const`.
  Needs tensor/dual bundles, `𝒪(k)`, ℙⁿ to state `T(L^{⊗k}) = k T(L)`.
- **Milestone 4 — finite branched covers `ρ : V → ℂ`** (the papers' setting). Since
  `∫_{∂V_r} u · ρ*(d^c log|t|²) = circleAverage (fibre-sum of u) 0 r` and
  `∑_{u ∈ V_s} ord_u H = ∑_{|t| ≤ s} (ρ_* H)(t)`, the parabolic theory reduces to push-forwards
  (`N_H = (deg ρ)⁻¹ · logCounting (ρ_* H)`, norms `Nm_ρ g` of meromorphic functions). Needs
  Riemann surfaces, finite holomorphic maps, degree, ramification divisor `div(ρ* dt)`.
- **Not planned**: SMT / defect relation for general `M` (Griffiths' conjecture). Cartan's SMT for
  `ℙⁿ` is a separate project (Wronskians, ℙⁿ, `𝒪(1)` on ℙⁿ).
