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

## 3. Work package WP0 — flat glue ✅ **DONE**

File `VD/Manifold/HolomorphicFlat.lean`.

Implemented 2026-08-28, slightly more general than planned (any `𝕜`, target a normed space `E'`):

```lean
theorem ContMDiffAt.analyticAt (h : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') ω f x) : AnalyticAt 𝕜 f x
theorem contMDiffAt_omega_iff_analyticAt [CompleteSpace E'] :
    ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') ω f x ↔ AnalyticAt 𝕜 f x
theorem contMDiff_omega_iff_analyticOnNhd :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') ω f ↔ AnalyticOnNhd 𝕜 f univ
theorem contMDiff_omega_iff_differentiable [CompleteSpace E] {f : ℂ → E} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) ω f ↔ Differentiable ℂ f
theorem contMDiffAt_omega_iff_eventually_differentiableAt [CompleteSpace E] {f : ℂ → E} {x : ℂ} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, E) ω f x ↔ ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ f z
```

Proofs: `contMDiffAt_iff_contDiffAt`, `contMDiff_iff_contDiff`, `ContDiffAt.analyticAt`,
`AnalyticAt.contDiffAt`, `contDiff_omega_iff_analyticOnNhd`,
`Complex.analyticOnNhd_univ_iff_differentiable`, `Complex.analyticAt_iff_eventually_differentiableAt`.

## 4. Work package WP1 — continuous norm bundles ✅ **DONE**

File `VD/Manifold/Bundle/ContinuousNorm.lean`. Variables as in Mathlib's Riemannian files,
fibre `F`, bundle `E : B → Type*`, `[∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]`,
`[FiberBundle F E] [VectorBundle 𝕜 F E]`.

Implemented 2026-08-28. The class needs only `[TopologicalSpace (TotalSpace F E)] [∀ x, Norm (E x)]`;
frame lemmas are stated for an arbitrary model fibre vector `y`, not just `1`:

```lean
class IsContinuousNormBundle (F E) : Prop where
  continuous_norm : Continuous (fun p : TotalSpace F E ↦ ‖p.2‖)
lemma ContinuousWithinAt.norm_bundle / ContinuousAt.norm_bundle / ContinuousOn.norm_bundle /
  Continuous.norm_bundle   -- norm of a continuous map `m ↦ (v m : TotalSpace F E)` into the fibres
lemma exists_norm_le_of_compactSpace [TopologicalSpace B] [CompactSpace B] {σ : ∀ x, E x}
    (hσ : Continuous (fun x ↦ (σ x : TotalSpace F E))) : ∃ C, ∀ x, ‖σ x‖ ≤ C
instance : IsContinuousNormBundle F₁ (Bundle.Trivial B F₁)                    -- F₁ normed group
instance [IsContinuousRiemannianBundle F₂ E₂] : IsContinuousNormBundle F₂ E₂
-- namespace Bundle.Trivialization, `e : Trivialization F₃ (π F₃ E₃)` `[e.IsLinear 𝕜]`:
theorem continuousOn_symmL (y : F₃) : ContinuousOn (fun x ↦ (e.symmL 𝕜 x y : TotalSpace F₃ E₃)) e.baseSet
theorem continuousOn_norm_symmL [IsContinuousNormBundle F₃ E₃] (y : F₃) :
    ContinuousOn (fun x ↦ ‖e.symmL 𝕜 x y‖) e.baseSet
theorem symmL_ne_zero (hb : b ∈ e.baseSet) (hy : y ≠ 0) : Trivialization.symmL 𝕜 e b y ≠ 0
theorem norm_symmL_pos (hb : b ∈ e.baseSet) (hy : y ≠ 0) : 0 < ‖Trivialization.symmL 𝕜 e b y‖
```

Lean notes: `Trivialization` lives in namespace `Bundle`; `continuousLinearMapAt_symmL` and
`symmL_apply` have `R` implicit, so inside `rw` pass `(R := 𝕜)` explicitly.

## 5. Work package WP2 — local coordinates and section ratios ✅ **DONE**

File `VD/Manifold/Bundle/LocalCoord.lean`. Line bundle `L : M → Type*` with fibre `ℂ`.

Implemented 2026-08-28, over a general field `𝕜` (source `𝕜`, bundle over a charted space `B`
modelled on `IB`), everything in `namespace Bundle`:

```lean
def localCoord (e : Trivialization F (π F E)) (σ : Π x, E x) (x : B) : F := (e ⟨x, σ x⟩).2
theorem localCoord_eq_continuousLinearMapAt [e.IsLinear 𝕜] (hx : x ∈ e.baseSet) :
    localCoord e σ x = e.continuousLinearMapAt 𝕜 x (σ x)
theorem symmL_localCoord [e.IsLinear 𝕜] (hx) : e.symmL 𝕜 x (localCoord e σ x) = σ x
theorem localCoord_eq_zero_iff [e.IsLinear 𝕜] (hx) : localCoord e σ x = 0 ↔ σ x = 0
theorem ContMDiffAt.localCoord_comp [ContMDiffVectorBundle n F E IB] [MemTrivializationAtlas e]
    (hf : ContMDiffAt IM IB n f x₀) (hσ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (σ x)) (f x₀))
    (he : f x₀ ∈ e.baseSet) : ContMDiffAt IM 𝓘(𝕜, F) n (localCoord e σ ∘ f) x₀
theorem ContMDiffAt.analyticAt_localCoord_comp [ContMDiffVectorBundle ω F E IB] {f : 𝕜 → B} … :
    AnalyticAt 𝕜 (localCoord e σ ∘ f) z
-- line bundles `L` (model fibre `𝕜`), `e e'` linear trivializations:
theorem eq_localCoord_smul_symmL (hx) : σ x = localCoord e σ x • e.symmL 𝕜 x 1
theorem norm_eq_norm_localCoord_mul (hx) : ‖σ x‖ = ‖localCoord e σ x‖ * ‖e.symmL 𝕜 x 1‖
theorem continuousLinearMapAt_symmL_one_ne_zero (hx) (hx') : e.continuousLinearMapAt 𝕜 x (e'.symmL 𝕜 x 1) ≠ 0
theorem localCoord_eq_localCoord_mul (hx) (hx') :
    localCoord e σ x = localCoord e' σ x * e.continuousLinearMapAt 𝕜 x (e'.symmL 𝕜 x 1)
noncomputable def sectionRatio (𝕜) (σ τ : Π x, L x) (x : B) : 𝕜     -- `𝕜` explicit (not inferable)
theorem sectionRatio_eq_div_localCoord (hx : x ∈ e.baseSet) :
    sectionRatio 𝕜 σ τ x = localCoord e σ x / localCoord e τ x
theorem sectionRatio_smul (hτ : τ x ≠ 0) : sectionRatio 𝕜 σ τ x • τ x = σ x
theorem norm_eq_norm_sectionRatio_mul (hτ : τ x ≠ 0) : ‖σ x‖ = ‖sectionRatio 𝕜 σ τ x‖ * ‖τ x‖
theorem sectionRatio_comp_eventuallyEq (hf : ContinuousAt f z) (he : f z ∈ e.baseSet) :
    sectionRatio 𝕜 σ τ ∘ f =ᶠ[𝓝 z] (localCoord e σ ∘ f) / (localCoord e τ ∘ f)
theorem ContMDiffAt.meromorphicAt_sectionRatio_comp [ContMDiffVectorBundle ω 𝕜 L IB] … :
    MeromorphicAt (sectionRatio 𝕜 σ τ ∘ f) z
theorem ContMDiffAt.analyticAt_sectionRatio_comp … (hτz : τ (f z) ≠ 0) : AnalyticAt 𝕜 (sectionRatio 𝕜 σ τ ∘ f) z
theorem ContMDiff.meromorphic_sectionRatio_comp … : Meromorphic (sectionRatio 𝕜 σ τ ∘ f)
```

Lean notes: trivialization independence was proved directly via the scalar transition factor
`e.continuousLinearMapAt 𝕜 x (e'.symmL 𝕜 x 1)` (no `coordChangeL` needed). Holomorphic sections
are hypotheses of the form `ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) ω (fun x ↦ TotalSpace.mk' F x (σ x))`,
matching Mathlib's `contMDiffAt_section_iff`. `continuousLinearMapAt`/`symmL` need `[FiberBundle F E]`;
`VectorBundle` is needed only for `trivializationAt` to be linear. Lemmas whose statement pins `𝕜` only
through `symmL 𝕜`/`IsLinear 𝕜` must be called with `(𝕜 := 𝕜)` inside `rw`/`conv`.

## 6. Work package WP3 — the divisor of `σ ∘ f` ✅ **DONE**

File `VD/Manifold/SectionDivisor.lean`.

Implemented 2026-08-28 in `VD/Manifold/SectionDivisor.lean`, namespace `Bundle` (not
`ValueDistribution`: nothing here is specific to value distribution), general field `𝕜`.

Design change: the junk-value condition of the divisor must not mention the model `IB` (it is not
inferable from `σ f`), so a new `IB`-free predicate carries the regularity:

```lean
noncomputable def sectionOrderAt (σ : Π x, L x) (f : 𝕜 → B) (z : 𝕜) : ℕ∞ :=
  analyticOrderAt (localCoord (trivializationAt 𝕜 L (f z)) σ ∘ f) z
def AnalyticAlong (σ) (f) : Prop :=          -- "σ ∘ f is a holomorphic section of f*L"
  Continuous f ∧ ∀ z, AnalyticAt 𝕜 (localCoord (trivializationAt 𝕜 L (f z)) σ ∘ f) z
theorem ContMDiff.analyticAlong (hf : ContMDiff 𝓘(𝕜) IB ω f) (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, 𝕜)) ω (T% σ)) :
    AnalyticAlong σ f
theorem sectionOrderAt_eq_zero_of_ne_zero (h : σ (f z) ≠ 0) : sectionOrderAt σ f z = 0
theorem sectionOrderAt_eq_zero_iff (hz : AnalyticAt 𝕜 (localCoord … σ ∘ f) z) : sectionOrderAt σ f z = 0 ↔ σ (f z) ≠ 0
theorem sectionOrderAt_eq_top_iff (hf : ContinuousAt f z) : sectionOrderAt σ f z = ⊤ ↔ ∀ᶠ w in 𝓝 z, σ (f w) = 0
theorem eventually_sectionOrderAt_eq_top (hf : Continuous f) (h : sectionOrderAt σ f z = ⊤) : ∀ᶠ w in 𝓝 z, sectionOrderAt σ f w = ⊤
theorem eventually_nhdsNE_sectionOrderAt_eq_zero (hf : ContinuousAt f z) (hz : AnalyticAt …) (h : … ≠ ⊤) :
    ∀ᶠ w in 𝓝[≠] z, sectionOrderAt σ f w = 0
theorem AnalyticAlong.sectionOrderAt_ne_top [PreconnectedSpace 𝕜] (h : AnalyticAlong σ f) (hne : ∃ z, σ (f z) ≠ 0) (z) :
    sectionOrderAt σ f z ≠ ⊤                    -- clopen argument, no global analytic function needed
theorem sectionOrderAt_eq_analyticOrderAt_localCoord (e) [MemTrivializationAtlas e] (hf : ContMDiffAt …) (hσ : …)
    (he : f z ∈ e.baseSet) : sectionOrderAt σ f z = analyticOrderAt (localCoord e σ ∘ f) z
noncomputable def sectionDivisor (σ) (f) : Function.locallyFinsupp 𝕜 ℤ
  -- value `(sectionOrderAt σ f z).toNat` if `AnalyticAlong σ f`, else `0`; order `⊤` ↦ `0` as in
  -- `MeromorphicOn.divisor`, so local finiteness needs no non-degeneracy hypothesis
theorem sectionDivisor_apply (h : AnalyticAlong σ f) : sectionDivisor σ f z = ((sectionOrderAt σ f z).toNat : ℤ)
theorem sectionDivisor_of_not (h : ¬ AnalyticAlong σ f) : sectionDivisor σ f = 0
theorem sectionDivisor_nonneg : 0 ≤ sectionDivisor σ f
theorem sectionDivisor_apply_eq_zero_of_ne_zero (h : σ (f z) ≠ 0) : sectionDivisor σ f z = 0
theorem sectionDivisor_sub_sectionDivisor_eq_divisor_sectionRatio (hf hσ hτ : ContMDiff …)
    (hσf : ∀ z, sectionOrderAt σ f z ≠ ⊤) (hτf : ∀ z, sectionOrderAt τ f z ≠ ⊤) :
    sectionDivisor σ f - sectionDivisor τ f = MeromorphicOn.divisor (sectionRatio 𝕜 σ τ ∘ f) univ
```

Also added to `LocalCoord.lean`: `ContMDiffAt.analyticAt_transition_comp` — the transition factor
`e.continuousLinearMapAt 𝕜 (f w) (e'.symmL 𝕜 (f w) 1)` is analytic in `w` (it is `coordChangeL`
applied to `1`, smooth by `ContMDiffVectorBundle.contMDiffOn_coordChangeL`).

Lean notes: `variable (σ f) in` orders explicit arguments by *declaration* order of the variables,
so declare `{σ τ …} {f …}` in that order. Use `ENat.ne_top_iff_exists`, not `WithTop.…`, to avoid a
`WithTop ℕ`/`ℕ∞` mismatch; `norm_cast` handles `(↑n - ↑m : WithTop ℤ).untop₀`.

## 7. Work package WP4 — proximity and counting ✅ **DONE**

Implemented 2026-08-28 in `VD/Manifold/Proximity.lean` and `VD/Manifold/Counting.lean`
(`𝕜 = ℂ` from here on; namespace `ValueDistribution`, integrability lemmas in `Bundle`):

```lean
-- general patching lemma (root namespace), reusable in Milestone 3:
theorem circleIntegrable_of_forall_exists_intervalIntegrable {u : ℂ → E} {c : ℂ} {R : ℝ}
    (h : ∀ θ : ℝ, ∃ δ > 0, IntervalIntegrable (fun θ ↦ u (circleMap c R θ)) volume (θ - δ) (θ + δ)) :
    CircleIntegrable u c R
theorem Bundle.AnalyticAlong.circleIntegrable_log_norm [IsContinuousNormBundle ℂ L] (h : AnalyticAlong σ f) (r) :
    CircleIntegrable (fun z ↦ log ‖σ (f z)‖) 0 r
theorem Bundle.AnalyticAlong.circleIntegrable_log_norm_inv … : CircleIntegrable (fun z ↦ log ‖σ (f z)‖⁻¹) 0 r
theorem Bundle.AnalyticAlong.eventually_ne_zero_codiscrete (h) (hσf : ∀ z, sectionOrderAt σ f z ≠ ⊤) :
    ∀ᶠ z in codiscrete 𝕜, σ (f z) ≠ 0                                   -- in SectionDivisor.lean
noncomputable def proximitySection (f : ℂ → B) (σ : Π x, L x) : ℝ → ℝ :=
  circleAverage (fun z ↦ log ‖σ (f z)‖⁻¹) 0
theorem proximitySection_sub_proximitySection (hσ hτ : AnalyticAlong _ f) (hσf hτf : ∀ z, sectionOrderAt _ f z ≠ ⊤)
    (hr : r ≠ 0) : proximitySection f τ r - proximitySection f σ r
      = circleAverage (fun z ↦ log ‖sectionRatio ℂ σ τ (f z)‖) 0 r      -- sign chosen to avoid `-circleAverage`
theorem neg_posLog_le_proximitySection (h : AnalyticAlong σ f) (hC : ∀ x, ‖σ x‖ ≤ C) (r) :
    -log⁺ C ≤ proximitySection f σ r                                    -- `log⁺` avoids a `1 ≤ C` side condition
theorem exists_le_proximitySection [CompactSpace B] (h) (hσ : Continuous (T% σ)) : ∃ c, ∀ r, c ≤ proximitySection f σ r
noncomputable def logCountingSection (f : ℂ → B) (σ : Π x, L x) : ℝ → ℝ := (sectionDivisor σ f).logCounting
theorem logCountingSection_eval_zero, logCountingSection_nonneg (hr : 1 ≤ r), logCountingSection_monotoneOn
theorem logCountingSection_sub_logCountingSection (hf hσ hτ : ContMDiff …) (hσf hτf) :
    logCountingSection f σ - logCountingSection f τ = (MeromorphicOn.divisor (sectionRatio ℂ σ τ ∘ f) univ).logCounting
```

Proof of integrability: at `θ₀`, with `e := trivializationAt ℂ L (f (circleMap 0 r θ₀))` and
`G := localCoord e σ ∘ f ∘ circleMap 0 r` (real-analytic at `θ₀`), either `G ≡ 0` near `θ₀` (then
`log ‖σ∘f‖ = 0` on a short arc) or `G ≠ 0` on a punctured neighbourhood; in the second case
`log‖σ∘f∘circleMap‖ = log‖G‖ + log‖frame‖` away from `θ₀` (`Real.log_mul` needs both factors
nonzero, hence the codiscrete congruence `intervalIntegrable_congr_codiscreteWithin`), with
`MeromorphicOn.intervalIntegrable_log_norm` for the first and `ContinuousOn.intervalIntegrable` for
the second summand.

Lean notes: `AnalyticAt.restrictScalars` has `𝕜` implicit (`(𝕜 := ℝ)`); `AnalyticAt.comp` needs
`(g := …) (f := …)` when the point is a `set`-variable (otherwise `circleMap` gets unfolded);
`Metric.eventually_nhds_iff` + `δ := ε/2` turns an `∀ᶠ` into an arc `[[θ₀ - δ, θ₀ + δ]]`;
`AnalyticAlong` and `sectionRatio` lemmas need `(𝕜 := ℂ)` inside `rw`; the style linter wants
`change`, not `show`, when the goal is modified.

## 8. Work package WP5 — characteristic, FMT, functoriality ✅ **DONE** (growth lemma deferred)

Implemented 2026-08-28 in `VD/Manifold/Characteristic.lean` (namespace `ValueDistribution`):

```lean
noncomputable def characteristicSection (f : ℂ → B) (σ : Π x, L x) : ℝ → ℝ :=
  proximitySection f σ + logCountingSection f σ
-- M1, exact First Main Theorem (hypotheses: hf hσ hτ : ContMDiff …, hσf hτf : ∀ z, sectionOrderAt _ f z ≠ ⊤)
theorem characteristicSection_sub_characteristicSection … (hR : R ≠ 0) :
    characteristicSection f σ R - characteristicSection f τ R
      = -log ‖meromorphicTrailingCoeffAt (sectionRatio ℂ σ τ ∘ f) 0‖
theorem isBigO_characteristicSection_sub_characteristicSection … :
    (characteristicSection f σ - characteristicSection f τ) =O[atTop] (1 : ℝ → ℝ)
-- metric independence (Lemma 4.6 analogue), via the ratio ρ of two continuous fibre norms:
theorem exists_abs_circleAverage_log_comp_le [CompactSpace B] (hf : Continuous f) (hρ : Continuous ρ)
    (hρ₀ : ∀ x, 0 < ρ x) : ∃ c, ∀ r, |circleAverage (fun z ↦ log (ρ (f z))) 0 r| ≤ c
-- M2, height functoriality (orbiBO Lem. A-2, Claim 7-17):
theorem characteristic_sectionRatio_le … (hσC : ∀ x, ‖σ x‖ ≤ C) (hτC : ∀ x, ‖τ x‖ ≤ C) (hr : 1 ≤ r) :
    characteristic (sectionRatio ℂ σ τ ∘ f) ⊤ r ≤ characteristicSection f τ r + 2 * log⁺ C
```

Proof of M1: WP4's two difference formulas plus Mathlib's Jensen
`logCounting_divisor_eq_circleAverage_sub_const`; `linarith` after `simp only [comp_apply]`.
Proof of M2: `(D_σ − D_τ)⁻ ≤ D_τ` pointwise (`negPart_eq_zero`/`negPart_eq_neg`, needs `1 ≤ r` for
`logCounting_le`) and the pointwise bound `log⁺‖σ/τ‖ ≤ 2 log⁺ C + log‖τ‖⁻¹`, which holds
*everywhere* on the circle (at zeros of `τ ∘ f` both sides are junk-friendly: the ratio is `0/0 = 0`),
so `circleAverage_mono` applies without codiscrete arguments.

**Deferred to Milestone 2:** the growth lemma (Lemma 4.7 analogue)
`(h : (σ/τ) ∘ f not constant) : ∃ c, ∀ r ≥ 1, log r ≤ characteristicSection f τ r + c`. It
reduces via M2 to the *classical* statement "`log r ≤ characteristic g ⊤ r + O(1)` for every
non-constant meromorphic `g`", which does not exist in Mathlib or the project yet (proof sketch:
pick `a`, `z₀` with `0 < meromorphicOrderAt (g · - a) z₀ < ⊤`, then
`N(r, a) ≥ log r − log ‖z₀‖` via `logCounting_single_eq_log_sub_const` + `logCounting_le`,
`m ≥ 0`, and the FMT shift `exists_abs_characteristic_coe_sub_characteristic_top_le` from
`VD/SMT/SecondMainTheorem.lean`; for `1 ≤ r ≤ ‖z₀‖` use `characteristic_monotoneOn`). It belongs
in the classical part of the library (candidate for `VD/MathlibPending`).

## 9. Work package WP6 — the Riemann sphere as a complex manifold ✅ **DONE**

Implemented 2026-08-28 in `VD/Manifold/RiemannSphere/Manifold.lean`, namespace `OnePoint`:

```lean
noncomputable def inv : OnePoint ℂ → OnePoint ℂ        -- ∞ ↦ 0, 0 ↦ ∞, z ↦ z⁻¹
theorem inv_infty, inv_coe_zero, inv_coe (hz : z ≠ 0), inv_inv, inv_involutive, inv_eq_infty_iff
theorem continuous_inv : Continuous inv
noncomputable def invHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ
noncomputable def chartCoe : OpenPartialHomeomorph (OnePoint ℂ) ℂ    -- (open embedding ℂ → ℙ¹).symm, source {∞}ᶜ
noncomputable def chartInv : OpenPartialHomeomorph (OnePoint ℂ) ℂ    -- invHomeomorph ≫ₕ chartCoe, source {0}ᶜ
theorem chartCoe_source, chartCoe_target, chartCoe_apply_coe, chartCoe_symm_apply,
  chartInv_apply, chartInv_symm_apply, chartInv_source, chartInv_target   (all @[simp])
instance instChartedSpace : ChartedSpace ℂ (OnePoint ℂ)   -- chartAt p := p.elim chartInv (fun _ ↦ chartCoe)
theorem chartAt_coe (z) : chartAt ℂ (z : OnePoint ℂ) = chartCoe, chartAt_infty : chartAt ℂ ∞ = chartInv  (rfl)
theorem mem_atlas_iff : e ∈ atlas ℂ (OnePoint ℂ) ↔ e = chartCoe ∨ e = chartInv
instance instIsManifold : IsManifold 𝓘(ℂ) ω (OnePoint ℂ)   -- transition maps id, id, z⁻¹, z⁻¹
theorem contMDiff_coe : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((↑) : ℂ → OnePoint ℂ)
theorem contMDiff_inv : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω inv
theorem contMDiffAt_coe_comp_iff {g : M → ℂ} :
    ContMDiffAt I 𝓘(ℂ) ω (fun x ↦ (g x : OnePoint ℂ)) x ↔ ContMDiffAt I 𝓘(ℂ) ω g x
```

Lean notes: inside `namespace OnePoint` the scoped notation `∞` clashes with `ContDiff`'s
`∞ : ℕ∞ω`, so the file does not `open scoped ContDiff` and uses a `local notation "ω"`.
`chartAt p := p.elim …` avoids `DecidableEq (OnePoint ℂ)`. Continuity of `inv` via
`OnePoint.continuous_iff`, `tendsto_inv₀_cobounded'`, `tendsto_inv₀_nhdsNE_zero`,
`nhdsNE_sup_pure`, and `coclosedCompact ℂ = cocompact ℂ = cobounded ℂ`. Holomorphy of `coe`/`inv`
via `contMDiffAt_iff_of_mem_source` with explicitly chosen charts. `contDiffOn_inv`/`contDiffAt_inv`
take `𝕜` explicitly. Not done (not needed so far): `contMDiffAt_iff` glue for maps *out of* the
sphere at `∞` (compose with `inv`).

## 10. Work package WP7 — meromorphic functions as maps to ℙ¹ ✅ **DONE**

Implemented 2026-08-28 in `VD/Manifold/RiemannSphere/OfMeromorphic.lean` (root namespace for the
definition, `Meromorphic.*` for the theorems):

```lean
noncomputable def toRiemannSphere (f : ℂ → ℂ) (z : ℂ) : OnePoint ℂ :=
  if 0 ≤ meromorphicOrderAt f z then ((toMeromorphicNFOn f univ z : ℂ) : OnePoint ℂ) else ∞
theorem toRiemannSphere_apply_of_nonneg (h : 0 ≤ meromorphicOrderAt f z) :
    toRiemannSphere f z = ((toMeromorphicNFOn f univ z : ℂ) : OnePoint ℂ)
theorem toRiemannSphere_apply_of_neg (h : meromorphicOrderAt f z < 0) : toRiemannSphere f z = ∞
theorem toRiemannSphere_eq_infty_iff : toRiemannSphere f z = ∞ ↔ meromorphicOrderAt f z < 0
theorem Meromorphic.toRiemannSphere_eventuallyEq_coe (hf : Meromorphic f) :
    toRiemannSphere f =ᶠ[codiscrete ℂ] fun z ↦ (f z : OnePoint ℂ)
theorem Meromorphic.contMDiff_toRiemannSphere (hf : Meromorphic f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toRiemannSphere f)
```

Proof of holomorphy at `z₀`: with `F := toMeromorphicNFOn f univ` (normal form, same orders as
`f`), if `0 ≤ ord`, then `F` is analytic near `z₀` and `toRiemannSphere f = (↑) ∘ F` there; if
`ord < 0`, then `F⁻¹` is analytic at `z₀` with `F⁻¹ z₀ = 0`, non-vanishing on a punctured
neighbourhood, and `toRiemannSphere f = OnePoint.inv ∘ (↑) ∘ F⁻¹` near `z₀` (splitting `𝓝 z₀ =
𝓝[≠] z₀ ⊔ pure z₀`). The converse ("every holomorphic `F : ℂ → ℙ¹` with `F ≢ ∞` is
`toRiemannSphere` of a meromorphic function") is not done; not needed for Milestone 1.

Lean notes: inside `theorem Meromorphic.…` the bare name `inv` resolves to `Meromorphic.inv`; write
`OnePoint.inv`. `meromorphicNFOn_toMeromorphicNFOn f U` takes `f U` explicitly.
`neg_nonneg` does not fire in `WithTop ℤ`; go through `WithTop.ne_top_iff_exists` + `norm_cast` +
`omega`.

## 11. Work package WP8 — `𝒪(1)`, Fubini–Study norm, sections `θ_a` ✅ **DONE**

Implemented 2026-08-28 in `VD/Manifold/RiemannSphere/Hyperplane.lean`, namespace `OnePoint`. The
`VectorBundleCore` route was taken (not the tautological-dual `VectorPrebundle` route): the bundle
structure and its holomorphy come for free from the core, and the Fubini–Study norm is put on the
fibres with Mathlib's `RiemannianBundle` mechanism (`InnerProductSpace.Core.toNormedAddCommGroupOfTopology`),
which works over `ℂ` and avoids the topology diamond.

```lean
noncomputable def transition : Bool → Bool → OnePoint ℂ → ℂ   -- false↔frame θ_∞ on {∞}ᶜ, true↔frame θ_0 on {0}ᶜ
def hyperplaneBaseSet : Bool → Set (OnePoint ℂ)               -- {∞}ᶜ, {0}ᶜ
def hyperplaneIndexAt : OnePoint ℂ → Bool                     -- true at ∞, false elsewhere
noncomputable def hyperplaneCore : VectorBundleCore ℂ (OnePoint ℂ) ℂ Bool  -- coordChange i j p = transition i j p • id
abbrev hyperplaneBundle : OnePoint ℂ → Type := hyperplaneCore.Fiber        -- 𝒪(1); fibres are ℂ definitionally
def coord {p} (v : hyperplaneBundle p) : ℂ, def ofCoord (p) (c : ℂ) : hyperplaneBundle p   -- explicit identifications
noncomputable def weight : OnePoint ℂ → ℝ                     -- 1/(1+‖z‖²) at z, 1 at ∞
noncomputable def fiberCore (p) : InnerProductSpace.Core ℂ (hyperplaneBundle p)   -- ⟪v,w⟫ = weight p * conj v * w
instance : NormedAddCommGroup (hyperplaneBundle p), InnerProductSpace ℂ (hyperplaneBundle p)
theorem norm_eq_sqrt_weight_mul (v) : ‖v‖ = √(weight p) * ‖coord v‖
noncomputable def rho : Bool → OnePoint ℂ → ℝ                 -- norm of the frame i at p
theorem norm_eq_rho_mul (hp : p ∈ hyperplaneBaseSet i) (v) : ‖v‖ = rho i p * ‖hyperplaneCore.coordChange (hyperplaneIndexAt p) i p v‖
instance : IsContinuousNormBundle ℂ hyperplaneBundle
theorem contMDiffOn_chartCoe, contMDiffOn_chartInv
instance hyperplaneCore.instIsContMDiff : hyperplaneCore.IsContMDiff 𝓘(ℂ) ω   -- hence ContMDiffVectorBundle ω
noncomputable def theta (a p : OnePoint ℂ) : hyperplaneBundle p   -- coord: z − a at z, 1 at ∞ (a finite); 1 at z, 0 at ∞ (a = ∞)
theorem theta_apply_eq_zero_iff : theta a p = 0 ↔ p = a
theorem norm_theta_infty_coe (z) : ‖theta ∞ z‖ = 1 / √(1 + ‖z‖ ^ 2), norm_theta_infty_infty : ‖theta ∞ ∞‖ = 0
theorem norm_theta_coe_coe (a z) : ‖theta a z‖ = ‖z - a‖ / √(1 + ‖z‖ ^ 2), norm_theta_coe_infty (a) : ‖theta a ∞‖ = 1
theorem contMDiff_theta (a) : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ)) ω (fun p ↦ TotalSpace.mk' ℂ p (theta a p))
```

Lean notes: instance search does not unfold `VectorBundleCore.Fiber`, so `HMul ℂ (hyperplaneBundle p)`
fails — always go through `coord`/`ofCoord` (all `rfl`-lemmas). `IsTopologicalAddGroup`/
`ContinuousConstSMul` on the fibres must be declared by `inferInstanceAs`. `Complex.conj_mul'` (not
`RCLike.conj_mul`) keeps the casts as `Complex.ofReal`. `contMDiffOn_chart` needs `(I := 𝓘(ℂ)) (H := ℂ)
(M := OnePoint ℂ) (x := …)`. `ContMDiffOn.inv₀`/`.smul`/`ContMDiffAt.mul` live in
`Geometry/Manifold/Algebra/{LieGroup,SMul,Structures}.lean`. Note `‖θ_a‖ ≤ 1` is *false* for finite
`a` (`|θ_a|² = |z−a|²/(1+|z|²)`); bounds come from compactness (`exists_norm_le_of_compactSpace`).

## 12. Work package WP9 — comparison with the classical theory ✅ **DONE**

Implemented 2026-08-28 in `VD/Manifold/Classical.lean` (namespace `ValueDistribution`, theorems in
`Meromorphic.*` for dot notation). Throughout `hf : Meromorphic f`, `F := toRiemannSphere f`, and
for finite `a` the non-degeneracy hypothesis `ha : ∃ z, toRiemannSphere f z ≠ a` (`f ≢ a`).

```lean
theorem abs_log_one_add_sq_div_two_sub_posLog_le (hx : 0 ≤ x) : |log (1 + x ^ 2) / 2 - log⁺ x| ≤ log 2 / 2
theorem abs_posLog_norm_sub_posLog_norm_sub_le (w a : ℂ) : |log⁺ ‖w‖ - log⁺ ‖w - a‖| ≤ log 2 + log⁺ ‖a‖
theorem Meromorphic.analyticAlong_theta (hf) (a) : AnalyticAlong (theta a) (toRiemannSphere f)
theorem Meromorphic.exists_toRiemannSphere_ne_infty (hf) : ∃ z, toRiemannSphere f z ≠ ∞
theorem Meromorphic.sectionOrderAt_theta_ne_top (hf) (ha : ∃ z, toRiemannSphere f z ≠ a) (z) : sectionOrderAt (theta a) F z ≠ ⊤
theorem OnePoint.sectionRatio_eq_coord_div (σ τ) (p) : sectionRatio ℂ σ τ p = coord (σ p) / coord (τ p)
theorem Meromorphic.sectionRatio_theta_comp_eventuallyEq (hf) (a : ℂ) :
    (sectionRatio ℂ (theta a) (theta ∞) ∘ F) =ᶠ[codiscrete ℂ] (f · - a)
theorem posPart_eq_and_negPart_eq_of_eq_sub …                        -- uniqueness of the Jordan decomposition in ℤ
theorem Meromorphic.sectionDivisor_theta_coe (hf) (ha) : sectionDivisor (theta a) F = (divisor (f · - a) univ)⁺
theorem Meromorphic.sectionDivisor_theta_infty (hf) : sectionDivisor (theta ∞) F = (divisor f univ)⁻   -- no hypothesis
theorem Meromorphic.logCountingSection_theta_infty (hf) : logCountingSection F (theta ∞) = logCounting f ⊤        -- exact
theorem Meromorphic.logCountingSection_theta_coe (hf) (ha) : logCountingSection F (theta a) = logCounting f a      -- exact
theorem Meromorphic.abs_proximitySection_theta_infty_sub_proximity_le (hf) (hr : r ≠ 0) :
    |proximitySection F (theta ∞) r - proximity f ⊤ r| ≤ log 2 / 2
theorem Meromorphic.abs_proximitySection_theta_coe_sub_proximity_le (hf) (ha) (hr : r ≠ 0) :
    |proximitySection F (theta a) r - proximity f a r| ≤ log 2 / 2 + (log 2 + log⁺ ‖a‖)
theorem Meromorphic.abs_characteristicSection_theta_infty_sub_characteristic_le (hf) (hr) :
    |characteristicSection F (theta ∞) r - characteristic f ⊤ r| ≤ log 2 / 2
theorem Meromorphic.abs_characteristicSection_theta_coe_sub_characteristic_le (hf) (ha) (hr) :
    |characteristicSection F (theta a) r - characteristic f a r| ≤ log 2 / 2 + (log 2 + log⁺ ‖a‖)
theorem Meromorphic.isBigO_characteristicSection_theta_infty_sub_characteristic (hf) :
    (characteristicSection F (theta ∞) - characteristic f ⊤) =O[atTop] (1 : ℝ → ℝ)
```

Proof of the divisor identities: no chart computation — the WP3 theorem gives
`D(θ_a) − D(θ_∞) = divisor ((θ_a/θ_∞) ∘ F) = divisor (f − a)` (codiscrete congruence), and since
`θ_a`, `θ_∞` never vanish simultaneously, uniqueness of the Jordan decomposition identifies the two
summands with `(divisor (f − a))⁺` and `(divisor (f − a))⁻`. The `θ_∞` statement needs no hypothesis
(the case `f ≡ 0` is handled separately). Proximity: the integrands agree codiscretely with
`log (1 + ‖f‖²)/2 − log⁺ ‖f − a‖`, which is bounded *everywhere* by the elementary inequalities, so
`circleAverage_mono` applies. The `r ≠ 0` hypothesis is needed for codiscrete congruence on the circle.

Lean notes: inside `namespace ValueDistribution`, `theorem Meromorphic.foo` becomes
`ValueDistribution.Meromorphic.foo` and dot notation `hf.foo` fails — use `_root_.Meromorphic.foo`.
`circleAverage_fun_sub` (lambda form) rather than `circleAverage_sub` (Pi form) matches `filter_upwards`
statements. `push_neg` is deprecated in favour of `push Not`.

**Milestone 1 complete (2026-08-28): WP0–WP9 all done; `lake build` of the whole project is clean.**

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
