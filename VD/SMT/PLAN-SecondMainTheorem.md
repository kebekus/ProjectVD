# Plan: The Second Main Theorem

Working plan for formalizing the *Second Main Theorem* (SMT) of Nevanlinna value
distribution theory — together with its first consumers, the defect relation and Picard's
little theorem — in a form that fits the existing Value Distribution library in
`Mathlib/Analysis/Complex/ValueDistribution/` and can be upstreamed as a sequence of
PR-sized pieces. Prepared 2026-07-09 against the Mathlib checkout in `.lake`
(commit `ae861491c1fc…`, toolchain v4.32.0-rc1). Companion to
`VD/LLD/PLAN-LogarithmicDerivative.md`, whose result
`ValueDistribution.isBigO_proximity_logDeriv` is the key analytic input here.

---

## 1. Goal

**Classical statements.** For `f` meromorphic on `ℂ` and a finite set `S ⊆ ℂ ∪ {∞}` of
targets,

```
(#S − 2) · T(r, f)  ≤  Σ_{a ∈ S} N̄(r, a)  +  O( log⁺ T(r, f) + log r )
```

as `r → ∞` outside a set of finite Lebesgue measure, where `N̄` is the *truncated*
(multiplicity-one) counting function. The finer intermediate statement, with the
ramification term (Lang's Theorem VII.2.1), for distinct **finite** targets `a₁, …, a_q`:

```
m(r, ∞) + Σⱼ m(r, aⱼ) + N₁(r)  ≤  2 · T(r, f)  +  O( log⁺ T(r, f) + log r ),
N₁(r) = N(r, 1/f′) + 2·N(r, f) − N(r, f′)      (the ramification term, ≥ 0).
```

Consequences targeted here as well: the **defect relation** `Σ_{a ∈ S} Θ(a) ≤ 2` for
transcendental `f`, and **Picard's little theorem** (a meromorphic function omitting three
values of `ℂ ∪ {∞}` is constant; an entire function omitting two finite values is
constant). References:

- Lang, *Introduction to Complex Hyperbolic Spaces* [MR886677], Ch. VII
  (pin exact section numbers when writing doc-strings);
- Hayman, *Meromorphic Functions* [MR164038], §2.1–2.4 (classical proof, defect relation);
- Cherry–Ye, *Nevanlinna's Theory of Value Distribution*, Ch. 4
  (sharp error terms — an optional refinement, not the target);
- Noguchi–Winkelmann [MR3156076], §2.3 (modern presentation).

**Formal targets.** Two new definitions and five headline theorems:

```lean
-- New definition 1: truncation of a divisor at multiplicity one.
noncomputable def Function.locallyFinsuppWithin.trunc
    (D : locallyFinsuppWithin U ℤ) : locallyFinsuppWithin U ℤ    -- z ↦ min (D z) 1

-- New definition 2: the truncated counting function N̄(r, a).
noncomputable def ValueDistribution.truncatedLogCounting (f : 𝕜 → E) (a : WithTop E) : ℝ → ℝ

-- (S1) The Second Main Theorem with ramification term (Lang's form).
theorem ValueDistribution.secondMainTheorem_ramification {f : ℂ → ℂ}
    (hf : Meromorphic f) (s : Finset ℂ) :
    ∃ c, ∀ᶠ r in volume.cofinite ⊓ atTop,
      proximity f ⊤ r + ∑ a ∈ s, proximity f a r
        + (logCounting (deriv f) 0 r + 2 * logCounting f ⊤ r - logCounting (deriv f) ⊤ r)
      ≤ 2 * characteristic f ⊤ r + c * (log⁺ (characteristic f ⊤ r) + Real.log r)

-- (S2) The Second Main Theorem, truncated headline form.
theorem ValueDistribution.secondMainTheorem {f : ℂ → ℂ}
    (hf : Meromorphic f) (S : Finset (WithTop ℂ)) :
    ∃ c, ∀ᶠ r in volume.cofinite ⊓ atTop,
      (S.card - 2 : ℝ) * characteristic f ⊤ r
        ≤ ∑ a ∈ S, truncatedLogCounting f a r
          + c * (log⁺ (characteristic f ⊤ r) + Real.log r)

-- (S2') posPart reformulation, a two-line corollary of S2 (and similarly of S1):
theorem ValueDistribution.secondMainTheorem_posPart {f : ℂ → ℂ}
    (hf : Meromorphic f) (S : Finset (WithTop ℂ)) :
    (fun r ↦ ((S.card - 2 : ℝ) * characteristic f ⊤ r
        - ∑ a ∈ S, truncatedLogCounting f a r)⁺)
      =O[volume.cofinite ⊓ atTop] fun r ↦ log⁺ (characteristic f ⊤ r) + Real.log r

-- (S3) The defect relation, for transcendental `f`.
theorem ValueDistribution.sum_truncatedDeficiency_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (h : Real.log =o[atTop] characteristic f ⊤) (S : Finset (WithTop ℂ)) :
    ∑ a ∈ S, truncatedDeficiency f a ≤ 2
-- + corollary sum_deficiency_le for the classical defects δ(a)

-- (S4) Picard's little theorem, entire version (flagship corollary; the meromorphic
-- three-value version stands behind it, see package H).
theorem Differentiable.exists_eq_const_of_forall_ne {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a b : ℂ} (hab : a ≠ b) (ha : ∀ z, f z ≠ a) (hb : ∀ z, f z ≠ b) :
    ∃ c, f = fun _ ↦ c
```

S1/S2 carry **no nondegeneracy hypothesis** on `f` (the eventually-constant case is
handled internally, see design decision 5), **no distinctness hypothesis** on the targets
(a `Finset` is distinct by construction), and **no cardinality hypothesis** (for
`#S ≤ 2` the same algebra goes through).

Sanity check (to be included as an `example` in package E): for `f = Complex.exp` and
`s = {0}`, both sides of S1 are `2·T(r) = 2r/π` up to `O(1)` — the SMT is *sharp* for the
exponential, with defects `δ(0) = δ(∞) = 1` summing exactly to `2`.

### Design decisions (and why)

1. **One-sided asymptotics via `∃ c, ∀ᶠ r in volume.cofinite ⊓ atTop, … ≤ … + c * (…)`.**
   The SMT is an inequality; the difference of the two sides is *not* two-sided `O` (the
   left side may be much smaller), and Mathlib's `Asymptotics` has no one-sided big-O.
   The explicit existential constant matches the style of the LLD two-radius theorem
   `exists_proximity_logDeriv_le` and is directly consumable for the defect relation
   (divide by `T`, take `limsup`). The posPart reformulations S1'/S2' are provided as
   corollaries for users who prefer a filter-algebra-composable `IsBigO` shape.
   No `+ 1` summand is needed in the error: eventually along the filter `1 ≤ log r`, so
   additive constants absorb into `c * log r`.

2. **Targets as `Finset (WithTop ℂ)` (S2, S3) resp. `Finset ℂ` (S1).** A `Finset` encodes
   distinctness by construction — no `Function.Injective` hypothesis as an indexed family
   `Fin q → ℂ` would need — and `∑ a ∈ S, …` matches the existing
   `proximity_sum_top_le` style. Note `(S.card − 2 : ℝ)` is a real-valued cast
   (`ℕ`-subtraction would truncate at `0` and weaken the statement for `#S ≤ 2`). The
   separation lemma (package C) extracts the minimum gap of the finite target set via
   `s.offDiag.inf'` internally.

3. **Both S1 and S2 are public headlines.** S1 is strictly finer — it retains the
   ramification term `N₁` and the un-truncated proximity data, and is the form needed for
   the strong defect relation with ramification. S2 is the quotable classic; its proof is
   pure bookkeeping from S1 + packages A/B + FMT, so having both costs one small file.

4. **Assembly at the filter level; no two-radius SMT.** Unlike the LLD, the SMT needs no
   new Borel-type argument: every error term is one of finitely many applications of the
   *already filter-level* LLD (`isBigO_proximity_logDeriv`) plus FMT constants, and
   `IsBigO.add` / `Filter.Eventually.and` compose them. Re-doing the two-radius plumbing
   would multiply the work for no consumer. An explicit-constant/two-radius SMT
   (Lang–Cherry sharp error terms) is a possible future refinement (§13), not a target.

5. **Hypothesis-free S1/S2 (only `hf : Meromorphic f`).** Degenerate case: if
   `meromorphicOrderAt (deriv f) x = ⊤` somewhere, then everywhere
   (`Meromorphic.exists_meromorphicOrderAt_eq_top_iff_forall`, applied to `hf.deriv`), and
   `f` is constant away from a discrete set (package D1). Then all `logCounting` terms
   vanish, the proximity terms are eventually constant, and the statement holds trivially
   because eventually `1 ≤ log r` (membership in the filter via `mem_inf_of_right`).
   Nondegenerate case: `∀ x, meromorphicOrderAt (deriv f) x ≠ ⊤`, so
   `{deriv f ≠ 0} ∈ codiscrete ℂ` (`MeromorphicOn.ne_zero_mem_codiscreteWithin`) and all
   junk-value identities hold codiscretely — the same discipline as in the LLD
   (`=ᶠ[codiscrete ℂ]` everywhere, consumed through `proximity_congr_codiscrete`).

6. **Where the truncation lives.** `trunc` is a ~40-line addition to
   `Mathlib/Topology/LocallyFinsupp.lean`. It cannot be the lattice `⊓` with a constant:
   the constant function `1` is *not* locally finitely supported. The file has no general
   `map`/composition operation either (verified), and building one is a larger design not
   needed here — `trunc` imitates the existing `Min` instance (LocallyFinsupp.lean:453),
   reusing `D`'s local-finiteness witnesses. The counting layer goes into a **new file**
   `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean`. **Level-1
   truncation only**: the literature's level-`k` functions `N_k` are a mechanical
   generalization (`min (D z) k`), to be added when a consumer arrives.

7. **No named `ramificationCounting` definition.** `N₁` appears inline in S1 as
   `logCounting (deriv f) 0 + 2 * logCounting f ⊤ − logCounting (deriv f) ⊤`; a definition
   would need its own API for a single use site. Package E provides `0 ≤ N₁ r` for
   `1 ≤ r` (cheap from package B), so users may simply drop the term.

8. **The defect relation hypothesizes transcendence**
   (`Real.log =o[atTop] characteristic f ⊤`). The `log r` in the SMT error term is
   *genuinely* not `o(T)` for rational `f` (where `T(r) ~ d·log r`), so S3 cannot follow
   from S2 for rational functions; classically their defect relation is a separate
   algebraic fact (Riemann–Hurwitz-flavoured), deferred as a follow-up (§13). The
   deficiencies themselves are defined with `limsup`/`liminf` along plain `atTop`; the
   exceptional set is bridged by the finer-filter comparison
   `volume.cofinite ⊓ atTop ≤ atTop` (limsup along a finer nontrivial filter is smaller).

9. **"`f` omits the value `a`" as a named predicate** `ValueDistribution.Omits f a` for
   `a : WithTop ℂ`, phrased through meromorphic orders — robust under junk values:
   `Omits f ⊤ ↔ ∀ x, 0 ≤ meromorphicOrderAt f x` (no poles) and
   `Omits f ↑a₀ ↔ ∀ x, meromorphicOrderAt (f · - a₀) x ≤ 0` (no `a₀`-points). This avoids
   `WithTop`-case-split hypotheses in the Picard statements and will be reused verbatim by
   the five-value theorem later. The entire-function corollary S4 is stated in plain
   `∀ z, f z ≠ a` terms, with a bridge lemma `Omits.of_forall_ne` for analytic functions.

10. **Names.** `secondMainTheorem` / `secondMainTheorem_ramification` follow the Mathlib
    precedent of naming famous results rather than fully descriptive names (hopeless
    here); doc-strings carry the descriptive content. Expect bikeshedding in review —
    nothing downstream depends on the names.

---

## 2. Inventory

### Already available (verified in the 2026-07-09 checkout)

| Ingredient | Name(s) |
|---|---|
| VD functions | `ValueDistribution.proximity/logCounting/characteristic` (+ `proximity_top/_coe/_zero/_inv`, `logCounting_zero/_top/_coe/_inv`, `characteristic = proximity + logCounting` definitionally) |
| FMT part 1 (inversion) | `characteristic_sub_characteristic_inv_le` (constant `max \|log ‖f 0‖\| \|log ‖meromorphicTrailingCoeffAt f 0‖\|`, junk-safe, no side conditions) |
| FMT part 2 (shift) | `abs_characteristic_sub_characteristic_shift_le` (constant `log⁺ ‖a₀‖ + log 2`) |
| Monotonicity, positivity of `T` | `characteristic_monotoneOn` (Cartan.lean), `characteristic_nonneg` (`1 ≤ r`), `proximity_nonneg`, `logCounting_nonneg` |
| THE LLD (T3) | `ValueDistribution.isBigO_proximity_logDeriv` (`VD/LLD/LogDerivLemma.lean`), hypothesis-free |
| `logDeriv` meromorphic API | `MeromorphicAt.logDeriv`, `meromorphicOrderAt_logDeriv_eq_neg_one/_nonneg`, `logDeriv_congr_codiscreteWithin`, `MeromorphicOn.ne_zero_mem_codiscreteWithin`, product→sum converters (`VD/LLD/MeromorphicLogDeriv.lean`) |
| Order of the derivative (pointwise) | `meromorphicOrderAt_deriv_eq_sub_one` (Order.lean, needs `(n : 𝕜) ≠ 0` — automatic over `ℂ`), `MeromorphicAt.deriv`, `Meromorphic.deriv`, `deriv_sub_const` |
| Order arithmetic | `meromorphicOrderAt_add_eq_left_of_lt`, `meromorphicOrderAt_const`, `meromorphicOrderAt_mul/_inv/_zpow` |
| Divisors | `MeromorphicOn.divisor` (`z ↦ (meromorphicOrderAt f z).untop₀`), lattice with `⁺`/`⁻` (`posPart_apply`, `negPart_apply`), `divisor_inv`, `divisor_congr_codiscreteWithin` |
| Divisor-level counting | `Function.locallyFinsuppWithin.logCounting : locallyFinsupp E ℤ →+ (ℝ → ℝ)` — an `AddMonoidHom`, so `map_add/map_sub/map_sum` are free; `logCounting_le` (needs `f₁ ≤ f₂`, `1 ≤ r`), `logCounting_mono`, `logCounting_nonneg` |
| Proximity arithmetic | `proximity_mul_top_le`, `proximity_sum_top_le` (error `log s.card`), `proximity_congr_codiscrete` (`r ≠ 0`) |
| `log⁺` toolkit | `posLog_mul`, `posLog_add`, `posLog_sum`, `posLog_le_posLog`, `Real.posLog_rpow`, `Real.abs_log_eq_posLog_add_posLog_inv` |
| Circle averages | `circleAverage_sum`, `circleAverage_mono`, `circleAverage_congr_codiscreteWithin`, `MeromorphicOn.circleIntegrable_posLog_norm` |
| Degeneracy tools | `Meromorphic.exists_meromorphicOrderAt_eq_top_iff_forall/_iff_eventually_zero` (`VD/MathlibPending/CharacteristicMoebius.lean`), `toMeromorphicNFOn` machinery, identity theorem `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, `IsOpen.is_const_of_fderiv_eq_zero` |
| Growth characterizations (pending) | `characteristic_isBigO_one_iff_constant` (`VD/MathlibPending/BoundednessCharacteristic.lean`), `rational_iff_characteristic_isBigO_log` (`VD/MathlibPending/CharacteristicIsBigOLog.lean`) |
| Fundamental thm. of algebra | `Complex.isAlgClosed`, `Polynomial.exists_root` |

### Missing (= the actual work, grouped into work packages A–H below)

- truncated divisor `trunc` + truncated counting function `truncatedLogCounting` (A);
- divisor of the derivative: `N(r, f′) = N(r, f) + N̄(r, ∞)` and
  `Σⱼ (N − N̄)(r, aⱼ) ≤ N(r, 1/f′)` (B) — the material explicitly reserved for the SMT
  by the docstring of `VD/LLD/MeromorphicLogDeriv.lean`;
- the pointwise separation lemma
  `Σⱼ log⁺ ‖w − aⱼ‖⁻¹ ≤ log⁺ ‖Σⱼ (w − aⱼ)⁻¹‖ + C(s)` (C);
- proximity estimates: constancy dichotomy, `m(r, f′/(f − a)) = S(r)` for each target,
  `m(r, f′) ≤ m(r, f) + m(r, f′/f)`, and the integrated separation bound (D);
- assembly of S1 (E) and of S2/S2' (F);
- deficiencies `δ`, `Θ` and the defect relation S3 (G);
- the omission predicate, the meromorphic three-value Picard theorem, and S4 (H).

---

## 3. Work package A — truncated divisors and truncated counting ✅ **DONE**

*New: ~40 lines extending `Mathlib/Topology/LocallyFinsupp.lean` + new file
`Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean`
(locally: `VD/SMT/TruncatedCounting.lean`). Independent of everything else.*

```lean
namespace Function.locallyFinsuppWithin
variable {X : Type*} [TopologicalSpace X] {U : Set X}

/-- Truncation of an integer-valued function with locally finite support: the pointwise
minimum with the constant `1`. This is *not* a lattice operation within
`locallyFinsuppWithin U ℤ`, because the constant function `1` does not have locally finite
support. -/
noncomputable def trunc (D : locallyFinsuppWithin U ℤ) : locallyFinsuppWithin U ℤ where
  toFun z := min (D z) 1
  supportWithinDomain' := …            -- support (min (D ·) 1) ⊆ support D ⊆ U
  supportLocallyFiniteWithinDomain' := …  -- reuse D's witness neighborhoods verbatim

@[simp] lemma trunc_apply (D : locallyFinsuppWithin U ℤ) (z : X) : D.trunc z = min (D z) 1
lemma trunc_le (D : locallyFinsuppWithin U ℤ) (h : 0 ≤ D) : D.trunc ≤ D
lemma trunc_nonneg {D : locallyFinsuppWithin U ℤ} (h : 0 ≤ D) : 0 ≤ D.trunc
lemma trunc_mono {D₁ D₂ : locallyFinsuppWithin U ℤ} (h : D₁ ≤ D₂) : D₁.trunc ≤ D₂.trunc
@[simp] lemma trunc_trunc (D : locallyFinsuppWithin U ℤ) : D.trunc.trunc = D.trunc
lemma support_trunc {D : locallyFinsuppWithin U ℤ} (h : 0 ≤ D) : D.trunc.support = D.support

-- counting layer (E a proper normed group, mirroring LogCounting/Basic.lean):
theorem logCounting_trunc_le {D : locallyFinsupp E ℤ} (h : 0 ≤ D) {r : ℝ} (hr : 1 ≤ r) :
    logCounting D.trunc r ≤ logCounting D r        -- logCounting_le (trunc_le h) hr
theorem logCounting_trunc_nonneg {D : locallyFinsupp E ℤ} (h : 0 ≤ D) {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ logCounting D.trunc r
end Function.locallyFinsuppWithin

namespace ValueDistribution   -- generality as in LogCounting/Basic.lean: f : 𝕜 → E
variable (f a) in
/-- The truncated logarithmic counting function `N̄(r, a)` of value distribution theory:
like `logCounting f a`, but counting each zero/pole once, regardless of multiplicity. -/
noncomputable def truncatedLogCounting : ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact ((divisor f Set.univ)⁻.trunc).logCounting
  · exact ((divisor (f · - a.untop₀) Set.univ)⁺.trunc).logCounting

lemma truncatedLogCounting_top / _coe / _zero      -- definition unfolding, as for logCounting
theorem truncatedLogCounting_le {r : ℝ} (hr : 1 ≤ r) :
    truncatedLogCounting f a r ≤ logCounting f a r
theorem truncatedLogCounting_nonneg {r : ℝ} (hr : 1 ≤ r) : 0 ≤ truncatedLogCounting f a r
theorem truncatedLogCounting_monotoneOn : MonotoneOn (truncatedLogCounting f a) (Set.Ioi 0)
@[simp] theorem truncatedLogCounting_inv {f : 𝕜 → 𝕜} :
    truncatedLogCounting f⁻¹ ⊤ = truncatedLogCounting f 0   -- divisor_inv, (−D)⁻ = D⁺
theorem truncatedLogCounting_congr_codiscrete {f g : ℂ → E} (h : f =ᶠ[codiscrete ℂ] g) :
    truncatedLogCounting f a = truncatedLogCounting g a
```

Sanity check: for `f = (·)^2`, the divisor is `2·δ₀`, its truncation is `δ₀`, and
`N̄(r, 0) = log r = ½·N(r, 0)` for `r ≥ 1`.

Proof notes: everything reduces to one-line pointwise `min`-arithmetic plus the existing
`logCounting_le/_nonneg/_mono` and `divisor_congr_codiscreteWithin`. The
`supportLocallyFiniteWithinDomain'` field reuses `D`'s witnesses verbatim (support
inclusion), exactly like the `Min` instance in `LocallyFinsupp.lean`. Note `trunc_le`
needs `0 ≤ D` (for `D z < 0` one has `min (D z) 1 = D z`, fine, but stating it with the
hypothesis keeps the intended use clear and the statement true also under `≤`-refactors);
all applications have `0 ≤ D` anyway since only `⁺`/`⁻`-parts are truncated.

Estimated size: ~280 lines. Difficulty: low.

---

## 4. Work package B — the divisor of the derivative ✅ **DONE**

*New file, eventually `Mathlib/Analysis/Meromorphic/DivisorDeriv.lean`
(locally: `VD/SMT/DivisorDeriv.lean`). Depends on A. This is the material explicitly
reserved for the SMT by the docstring of `VD/LLD/MeromorphicLogDeriv.lean`.*

Order-level lemmas (generality `f : 𝕜 → E` with `[CompleteSpace E]`, `[CharZero 𝕜]` where
division matters, mirroring the LLD order section):

```lean
/-- Derivatives of locally vanishing functions vanish locally. -/
theorem meromorphicOrderAt_deriv_eq_top {f : 𝕜 → E} (h : meromorphicOrderAt f x = ⊤) :
    meromorphicOrderAt (deriv f) x = ⊤
  -- f =ᶠ[𝓝[≠] x] 0 ⇒ deriv f =ᶠ[𝓝[≠] x] 0, same device as in MeromorphicLogDeriv.lean

/-- Where a meromorphic function has nonnegative order, so does its derivative. -/
theorem meromorphicOrderAt_deriv_nonneg {f : 𝕜 → E} (hf : MeromorphicAt f x)
    (h : 0 ≤ meromorphicOrderAt f x) : 0 ≤ meromorphicOrderAt (deriv f) x
  -- cases: order = ⊤ (above); order = n ≥ 1 (meromorphicOrderAt_deriv_eq_sub_one);
  -- order = 0 (congruence to an analytic representative, as in
  -- meromorphicOrderAt_logDeriv_nonneg)
```

Divisor-level results (the mathematical core of the truncation bookkeeping):

```lean
/-- **Pole divisor of the derivative**: the poles of `deriv f` are exactly the poles of
`f`, with multiplicity increased by exactly one. -/
theorem MeromorphicOn.negPart_divisor_deriv {f : 𝕜 → E} (hf : MeromorphicOn f U) :
    (divisor (deriv f) U)⁻ = (divisor f U)⁻ + ((divisor f U)⁻).trunc
  -- pointwise, with n := meromorphicOrderAt f z:
  --   n = ⊤:        both sides 0        (meromorphicOrderAt_deriv_eq_top)
  --   0 ≤ n < ⊤:    both sides 0        (meromorphicOrderAt_deriv_nonneg)
  --   n < 0:        LHS = −(n−1) = (−n) + 1 = RHS   (meromorphicOrderAt_deriv_eq_sub_one)

/-- At most one target is attained at any point: helper for disjointness of supports. -/
theorem meromorphicOrderAt_sub_const_eq_zero_of_ne {f : 𝕜 → 𝕜} {a b : 𝕜} (hab : b ≠ a)
    (h : 0 < meromorphicOrderAt (f · - a) x) : meromorphicOrderAt (f · - b) x = 0
  -- (f · − b) = (fun _ ↦ a − b) + (f · − a); meromorphicOrderAt_add_eq_left_of_lt with
  -- meromorphicOrderAt_const (order 0 of the constant a − b ≠ 0 beats the positive order)

/-- **Zero divisor of the derivative**, one target: an `a`-point of `f` of multiplicity
`m` is a zero of `deriv f` of multiplicity `m − 1`. -/
theorem MeromorphicOn.posPart_divisor_sub_trunc_le_divisor_deriv {f : 𝕜 → 𝕜} {a : 𝕜}
    (hf : MeromorphicOn f U) :
    (divisor (f · - a) U)⁺ - ((divisor (f · - a) U)⁺).trunc ≤ (divisor (deriv f) U)⁺
  -- pointwise: m ≤ 0 or ⊤ ⇒ LHS = 0 ≤ RHS; m ≥ 1 ⇒ deriv (f · − a) = deriv f
  -- (deriv_sub_const), order (deriv f) = m − 1 ≥ 0, RHS = m − 1 = LHS

/-- **Zero divisor of the derivative**, several targets (disjoint supports). -/
theorem MeromorphicOn.sum_posPart_divisor_sub_trunc_le_divisor_deriv {f : 𝕜 → 𝕜}
    (hf : MeromorphicOn f U) (s : Finset 𝕜) :
    ∑ a ∈ s, ((divisor (f · - a) U)⁺ - ((divisor (f · - a) U)⁺).trunc)
      ≤ (divisor (deriv f) U)⁺
  -- pointwise: by …_eq_zero_of_ne, at most one summand is nonzero at each z;
  -- reduce to the one-target lemma
```

Sanity check: `f = (·)⁻¹` has order `−1` at `0`; `deriv f = −(·)⁻²` has order `−2`; the
negative parts are `1 ↦ 2 = 1 + min 1 1`. ✓

Counting-function corollaries (namespace `ValueDistribution`, `f : ℂ → ℂ`):

```lean
/-- `N(r, f′) = N(r, f) + N̄(r, f)`: exact equality of functions. -/
theorem logCounting_deriv_top {f : ℂ → ℂ} (hf : Meromorphic f) :
    logCounting (deriv f) ⊤ = logCounting f ⊤ + truncatedLogCounting f ⊤
  -- rewrite via logCounting_top, negPart_divisor_deriv, and map_add of the
  -- AddMonoidHom Function.locallyFinsuppWithin.logCounting

/-- `Σⱼ (N(r, aⱼ) − N̄(r, aⱼ)) ≤ N(r, 1/f′)`: multiple points are zeros of `f′`. -/
theorem sum_logCounting_sub_truncatedLogCounting_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (s : Finset ℂ) {r : ℝ} (hr : 1 ≤ r) :
    ∑ a ∈ s, (logCounting f a r - truncatedLogCounting f a r)
      ≤ logCounting (deriv f) 0 r
  -- map_sub/map_sum of logCounting, then divisor-level logCounting_le with the
  -- several-targets inequality; logCounting (deriv f) 0 = ((divisor (deriv f) univ)⁺).…
```

Estimated size: ~350 lines (`WithTop ℤ` / `untop₀` case analyses dominate).
Difficulty: medium.

---

## 5. Work package C — the separation lemma ✅ **DONE**

*Pure elementary analysis, no meromorphy. Locally `VD/SMT/SeparationLemma.lean`; Mathlib
target: extend `Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean` (fallback: fold into
the SMT file, see §12). Independent of everything else. Stated over a general
`NormedField` (weaker than the planned `NontriviallyNormedField` — the proof only uses
the triangle inequality and multiplicativity of the norm), in `namespace Real` following
the precedent of `posLog_norm_sum_le`. Implemented with one public helper,
`Real.sum_posLog_norm_inv_sub_le` (the "far from all targets" bound), reused for both
case (i) and the tail estimate of case (ii).*

```lean
/-- **Separation lemma**: for a finite set `s` of points, closeness to one point of `s`,
measured by `Σ_a log⁺ ‖· − a‖⁻¹`, is detected by the single function
`log⁺ ‖Σ_a (· − a)⁻¹‖`, up to a constant depending only on `s`. Key pointwise input for
the Second Main Theorem. -/
theorem exists_sum_posLog_norm_inv_sub_le {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (s : Finset 𝕜) :
    ∃ C, ∀ w : 𝕜, ∑ a ∈ s, log⁺ ‖w - a‖⁻¹ ≤ log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ + C
```

Proof sketch (Lang VII §2 / Hayman §2.1; each numbered step a lemma-sized piece):

1. `q := s.card`. Case `q ≤ 1`: `C := 0` works (`q = 0` trivial; `q = 1` is an equality).
2. `q ≥ 2`: set `δ := min 1 (s.offDiag.inf' … fun p ↦ dist p.1 p.2)` (the `offDiag` is
   nonempty since `1 < q`); then `0 < δ ≤ 1` and `δ ≤ ‖a − b‖` for distinct `a, b ∈ s`.
   Take `C := q * log⁺ (2 * q / δ) + Real.log q`.
3. **Case (i)** `∀ a ∈ s, δ/(2*q) ≤ ‖w − a‖`: each summand is `≤ log⁺ (2q/δ)`, so
   LHS `≤ q · log⁺ (2q/δ) ≤ C`, while RHS `≥ 0` (`posLog_nonneg`).
4. **Case (ii)** `∃ a₀ ∈ s, ‖w − a₀‖ < δ/(2*q)`: for `b ∈ s`, `b ≠ a₀`, the triangle
   inequality gives `δ/2 ≤ ‖w − b‖` (using `δ/(2q) ≤ δ/2`), so
   `Σ_{b ≠ a₀} log⁺ ‖w − b‖⁻¹ ≤ (q−1) · log⁺ (2/δ)`.
5. Sub-case `w = a₀`: in Lean `‖w − a₀‖⁻¹ = 0⁻¹ = 0` and `log⁺ 0 = 0` — the junk-value
   convention makes the statement true for *all* `w` with no side condition; step 4's
   bound alone suffices. (This is why package D needs no codiscrete comparison for the
   integration step.)
6. Sub-case `w ≠ a₀`, dominance of the singular term:
   `‖Σ_a (w−a)⁻¹‖ ≥ ‖w−a₀‖⁻¹ − (q−1)·(2/δ) ≥ (1/q)·‖w−a₀‖⁻¹`, since
   `‖w−a₀‖⁻¹ > 2q/δ` gives `(q−1)·(2/δ) ≤ ((q−1)/q)·‖w−a₀‖⁻¹`. Then
   `log⁺ ‖w−a₀‖⁻¹ ≤ log⁺ (q · ‖Σ_a (w−a)⁻¹‖) ≤ Real.log q + log⁺ ‖Σ_a (w−a)⁻¹‖`
   (`posLog_mul`, `1 ≤ q`); add step 4's bound for the remaining terms.

Estimated size: ~230 lines. Difficulty: medium (elementary, but the case analysis and the
`Finset` bookkeeping must be organized carefully; the existential constant removes all
pressure to optimize).

---

## 6. Work package D — proximity estimates ✅ **DONE**

*Locally `VD/SMT/ProximityEstimates.lean`; Mathlib target
`Analysis/Complex/ValueDistribution/SecondMainTheorem.lean` (part 1). Depends on C,
the LLD, FMT part 2, and (D1 only) the pending `CharacteristicMoebius` chain.
Implementation notes: package B turned out not to be needed — the only order-level input
is `meromorphicOrderAt_deriv_eq_sub_one`, which is already in Mathlib. The "15-line
adaptation of `logDeriv_congr_codiscreteWithin`" anticipated for D1 is included as the
public lemma `deriv_congr_codiscreteWithin` (Mathlib-worthy on its own; possible target
near `Mathlib/Analysis/Calculus/Deriv/Basic.lean`). Everything else went as planned;
the junk-value identities of D3/D4 survived Lean's `x/0 = 0` conventions exactly as
predicted in risk 2.*

### D1. The constancy dichotomy

```lean
/-- A meromorphic function on `ℂ` whose derivative vanishes somewhere to infinite order
is constant away from a discrete set. -/
theorem Meromorphic.eventuallyEq_const_of_exists_meromorphicOrderAt_deriv_eq_top
    {f : ℂ → ℂ} (hf : Meromorphic f) (h : ∃ x, meromorphicOrderAt (deriv f) x = ⊤) :
    ∃ c, f =ᶠ[codiscrete ℂ] fun _ ↦ c
```

Proof sketch: `h` upgrades to `∀ x` (`exists_meromorphicOrderAt_eq_top_iff_forall` for
`hf.deriv`). Then no `x` has `meromorphicOrderAt f x < 0` or `∈ (0, ⊤)` (else
`meromorphicOrderAt_deriv_eq_sub_one` would give finite deriv-order). Two cases: some `x`
has order `⊤` — then `f =ᶠ[codiscrete ℂ] 0` directly (`…_iff_eventually_zero`); or the
order of `f` is `0` everywhere — pass to `g := toMeromorphicNFOn f Set.univ`
(`g =ᶠ[codiscrete ℂ] f`, analytic on all of `ℂ` since in normal form with order `0`
everywhere), transfer `deriv g =ᶠ[codiscrete ℂ] deriv f =ᶠ 0` (deriv-congruence on open
codiscrete sets: 15-line adaptation of `logDeriv_congr_codiscreteWithin`), kill `deriv g`
identically by the identity theorem
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, `ℂ` preconnected),
conclude `g` constant (`IsOpen.is_const_of_fderiv_eq_zero` over `ℝ` via
`HasDerivAt.hasFDerivAt`). This route deliberately avoids
connectedness-of-complement arguments.

### D2. The `S(r)` lemma for shifted logarithmic derivatives

```lean
/-- `m(r, f′/(f − a)) = S(r)`: the Lemma on the Logarithmic Derivative for `f − a`, with
the error expressed through the characteristic of `f` itself. -/
theorem ValueDistribution.isBigO_proximity_logDeriv_shift {f : ℂ → ℂ}
    (hf : Meromorphic f) (a : ℂ) :
    proximity (logDeriv (f · - a)) ⊤ =O[volume.cofinite ⊓ atTop]
      fun r ↦ log⁺ (characteristic f ⊤ r) + Real.log r
```

Proof: `isBigO_proximity_logDeriv` for `f · − a` (meromorphic by `hf.sub`), then transport
the comparison function: `characteristic (f · − a) ⊤ r ≤ characteristic f ⊤ r + (log⁺ ‖a‖
+ log 2)` (FMT part 2), so `log⁺ (characteristic (f·−a) ⊤ r) ≤ log 2 + log⁺
(characteristic f ⊤ r) + log⁺ (log⁺ ‖a‖ + log 2)` (`posLog_add`, `posLog_le_posLog` with
`characteristic_nonneg` for `1 ≤ r`); conclude with `IsBigO.trans` and eventual
`1 ≤ log r` to absorb constants. Already a citable statement on its own
("the LLD for arbitrary finite targets").

### D3. Proximity of the derivative

```lean
/-- `m(r, f′) ≤ m(r, f) + m(r, f′/f)`. -/
theorem ValueDistribution.proximity_deriv_top_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (h' : ∀ x, meromorphicOrderAt f x ≠ ⊤) {r : ℝ} (hr : r ≠ 0) :
    proximity (deriv f) ⊤ r ≤ proximity f ⊤ r + proximity (logDeriv f) ⊤ r
```

Proof: `deriv f =ᶠ[codiscrete ℂ] f * logDeriv f` — pointwise wherever `f` is analytic and
`f z ≠ 0` (codiscrete by `h'` and `MeromorphicOn.ne_zero_mem_codiscreteWithin`); then
`proximity_congr_codiscrete hr` and `proximity_mul_top_le`.

### D4. Integrated separation bound

```lean
/-- `Σⱼ m(r, aⱼ) ≤ m(r, 1/f′) + Σⱼ m(r, f′/(f − aⱼ)) + c`. -/
theorem ValueDistribution.sum_proximity_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (h' : ∀ x, meromorphicOrderAt (deriv f) x ≠ ⊤) (s : Finset ℂ) :
    ∃ c, ∀ r : ℝ, 1 ≤ r →
      ∑ a ∈ s, proximity f a r
        ≤ proximity (deriv f)⁻¹ ⊤ r
          + ∑ a ∈ s, proximity (logDeriv (f · - a)) ⊤ r + c
```

Proof chain, each step lemma-sized:

1. `∑ a ∈ s, proximity f a r = circleAverage (fun z ↦ ∑ a ∈ s, log⁺ ‖f z − a‖⁻¹) 0 r`
   (`proximity_coe`, `circleAverage_sum`; integrability of each summand from
   `MeromorphicOn.circleIntegrable_posLog_norm` applied to `(f · − a)⁻¹`, using
   `‖(f z − a)⁻¹‖ = ‖f z − a‖⁻¹`).
2. Apply package C **pointwise at `w := f z` for every `z` on the circle** (the
   separation lemma holds for all `w`, junk values included) and `circleAverage_mono`:
   `… ≤ circleAverage (fun z ↦ log⁺ ‖∑ a ∈ s, (f z − a)⁻¹‖) 0 r + C_s`. The auxiliary
   function `F := fun z ↦ ∑ a ∈ s, (f z − a)⁻¹` is meromorphic (sum/inv/sub-const
   closure), so `log⁺ ‖F ·‖` is circle-integrable. *No codiscrete-monotone comparison
   needed here* (see C, step 5).
3. `F =ᶠ[codiscrete ℂ] (deriv f)⁻¹ * ∑ a ∈ s, logDeriv (f · - a)`: pointwise wherever
   `deriv f z ≠ 0` (codiscrete by `h'` + `ne_zero_mem_codiscreteWithin`), because
   `logDeriv (f · − a) z = deriv f z / (f z − a)` (`deriv_sub_const`) and — thanks to
   Lean's `x/0 = 0 = 0⁻¹` conventions — the identity
   `(deriv f z)⁻¹ * (deriv f z / (f z − a)) = (f z − a)⁻¹` holds *even at points with
   `f z = a`*. Then `proximity_congr_codiscrete` (`r ≠ 0`).
4. `proximity_mul_top_le` and `proximity_sum_top_le` (error `Real.log s.card`). Total
   constant `c := C_s + Real.log s.card`.

Estimated size: D1 ≈ 90, D2 ≈ 60, D3 ≈ 40, D4 ≈ 140; total ~330 lines.
Difficulty: medium (D1 is the only delicate proof; D4 is long but mechanical).

---

## 7. Work package E — the SMT with ramification (S1) ✅ **DONE**

*Locally `VD/SMT/SecondMainTheoremRamification.lean`; Mathlib target
`…/ValueDistribution/SecondMainTheorem.lean` (part 2). Depends on B (for
`meromorphicOrderAt_deriv_eq_top` and the nonnegativity of `N₁`) and D; uses FMT part 1
and the LLD.
Implementation notes: proof went exactly as planned (degenerate case via D1, main case
via FMT-1 + D3 + D4 + one combined `IsBigO` for the LLD and all D2 instances, assembled
by `nlinarith`). The posPart corollary S1′ is included as
`secondMainTheorem_ramification_posPart`. The sanity example verifies that all counting
terms — in particular the ramification term — vanish identically for `Complex.exp`; the
sharpness statement `T(r, exp) = r/π` would require computing a circle integral and is
not formalized.*

Statement S1 as in §1, plus its posPart corollary and:

```lean
/-- The ramification term of the Second Main Theorem is nonnegative. -/
theorem ValueDistribution.ramification_nonneg {f : ℂ → ℂ} (hf : Meromorphic f)
    {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ logCounting (deriv f) 0 r + 2 * logCounting f ⊤ r - logCounting (deriv f) ⊤ r
  -- via logCounting_deriv_top (B): the term equals N(r,1/f′) + N(r,f) − N̄(r,f) ≥ 0
```

Proof of S1:

1. **Degenerate case** `∃ x, meromorphicOrderAt (deriv f) x = ⊤`: D1 gives
   `f =ᶠ[codiscrete ℂ] const c₀`. Eventually along the filter (`1 ≤ r`, so `r ≠ 0`):
   `proximity f ⊤ r = log⁺ ‖c₀‖` and `proximity f a r = log⁺ ‖c₀ − a‖⁻¹` (congruence +
   `proximity_const`); all three `logCounting` terms vanish (the order of `deriv f` is `⊤`
   everywhere, so `divisor (deriv f) Set.univ = 0`; congruence + `logCounting_const` for
   `f`); `characteristic f ⊤ r ≥ 0`. The LHS is eventually a constant `B`, and `c := B`
   works since eventually `1 ≤ log r`.
2. **Main case** `h' : ∀ x, meromorphicOrderAt (deriv f) x ≠ ⊤` (also
   `∀ x, meromorphicOrderAt f x ≠ ⊤` by contraposition with
   `meromorphicOrderAt_deriv_eq_top`).
3. FMT part 1 for `deriv f` (`characteristic_sub_characteristic_inv_le`):
   `proximity (deriv f)⁻¹ ⊤ r + logCounting (deriv f) 0 r
     ≤ proximity (deriv f) ⊤ r + logCounting (deriv f) ⊤ r + c₁` for all `r`
   (using `characteristic = proximity + logCounting`, `logCounting_inv`, `proximity_inv`).
4. D3: `proximity (deriv f) ⊤ r ≤ proximity f ⊤ r + proximity (logDeriv f) ⊤ r`
   (`r ≠ 0` eventually).
5. D4: `∑ a ∈ s, proximity f a r ≤ proximity (deriv f)⁻¹ ⊤ r
     + ∑ a ∈ s, proximity (logDeriv (f·−a)) ⊤ r + c₂`.
6. The LLD for `f` and D2 for each `a ∈ s`: via `isBigO_iff`, eventual bounds
   `proximity (logDeriv …) ⊤ r ≤ c₃ · (log⁺ (characteristic f ⊤ r) + log r)`; intersect
   the finitely many eventual sets (`Filter.Eventually.and` / `eventually_all_finset`).
7. Linear arithmetic: add
   `proximity f ⊤ + (logCounting (deriv f) 0 + 2·logCounting f ⊤ − logCounting (deriv f) ⊤)`
   to 5, cancel through 3–4 using `characteristic f ⊤ = proximity f ⊤ + logCounting f ⊤`
   (definitional), obtaining `≤ 2 · characteristic f ⊤ r + (Σ of S-terms) + c₁ + c₂`;
   absorb additive constants with `1 ≤ log r`.

Sanity `example` (see §1): for `f = Complex.exp`, `s = {0}` the inequality is sharp up to
the error term.

Estimated size: ~350 lines. Difficulty: medium (pure bookkeeping; the analysis is all in
C/D).

---

## 8. Work package F — the truncated SMT (S2)

*Locally `VD/SMT/SecondMainTheorem.lean`; Mathlib target
`…/ValueDistribution/SecondMainTheorem.lean` (part 3). Depends on A, B, E; uses FMT
parts 1 + 2.*

Helpers (both flagged for possible upstreaming into `FirstMainTheorem.lean`):

```lean
/-- The characteristic for a finite value is the characteristic of the shifted inverse. -/
lemma ValueDistribution.characteristic_coe_eq_characteristic_shift_inv {f : ℂ → ℂ}
    {a₀ : ℂ} : characteristic f a₀ = characteristic (f · - a₀)⁻¹ ⊤
  -- proximity_coe/proximity_inv + logCounting_coe/logCounting_inv; essentially definitional

/-- **First Main Theorem, combined form**: for every finite value, the characteristic
differs from `characteristic f ⊤` by a bounded function. -/
theorem ValueDistribution.exists_abs_characteristic_coe_sub_characteristic_top_le
    {f : ℂ → ℂ} (hf : Meromorphic f) (a₀ : ℂ) :
    ∃ C, ∀ r, |characteristic f a₀ r - characteristic f ⊤ r| ≤ C
  -- chain: characteristic f a₀ = characteristic (f·−a₀)⁻¹ ⊤ ≈₁ characteristic (f·−a₀) ⊤
  --        ≈₂ characteristic f ⊤, with ≈₁ = FMT part 1 and ≈₂ = FMT part 2
```

Proof of S2 from S1:

1. Split `S`: let `s : Finset ℂ := S.preimage (↑·) WithTop.coe_injective.injOn`; then
   `∑ a ∈ S, truncatedLogCounting f a r
     = (if ⊤ ∈ S then truncatedLogCounting f ⊤ r else 0)
       + ∑ a ∈ s, truncatedLogCounting f ↑a r`
   and `(S.card : ℝ) = s.card + (if ⊤ ∈ S then 1 else 0)` (`Finset` plumbing).
2. Apply S1 with `s`; fix its constant and eventual set.
3. For each `a ∈ s`: `proximity f a r = characteristic f a r − logCounting f a r
     ≥ characteristic f ⊤ r − logCounting f a r − C_a` (combined FMT above); and exactly
   `proximity f ⊤ r = characteristic f ⊤ r − logCounting f ⊤ r`.
4. Package B, counting level (`1 ≤ r` eventually):
   `∑ a ∈ s, logCounting f a r ≤ ∑ a ∈ s, truncatedLogCounting f a r
     + logCounting (deriv f) 0 r` and
   `logCounting (deriv f) ⊤ r − 2·logCounting f ⊤ r = −logCounting f ⊤ r
     + truncatedLogCounting f ⊤ r` (exact, from `logCounting_deriv_top`).
5. Combine 2–4:
   `((s.card : ℝ) + 1 − 2) * characteristic f ⊤ r
     ≤ ∑ a ∈ s, truncatedLogCounting f ↑a r + truncatedLogCounting f ⊤ r
       + Σ_a C_a + c · (log⁺ T r + log r)`.
6. If `⊤ ∈ S`, this is the claim. If `⊤ ∉ S`, drop the `⊤`-term via
   `truncatedLogCounting f ⊤ r ≤ logCounting f ⊤ r ≤ characteristic f ⊤ r`
   (A + `proximity_nonneg`), moving one `T` to the left.
7. Absorb `Σ_a C_a` using `1 ≤ log r` eventually. The posPart corollary S2' follows in two
   lines: `x ≤ c·g` with `g ≥ 0` gives `|x⁺| ≤ c·g`, then `isBigO_iff`.

Estimated size: ~300 lines. Difficulty: low–medium (`Finset (WithTop ℂ)` plumbing is the
only annoyance).

---

## 9. Work package G — deficiency and the defect relation (S3)

*Locally `VD/SMT/Deficiency.lean`; Mathlib target: new file
`…/ValueDistribution/Deficiency.lean`. Depends on A (definitions) and F (S2).*

```lean
namespace ValueDistribution   -- generality f : ℂ → E where meaningful

/-- The **Nevanlinna deficiency** `δ(a)` of a value `a`: the density of `r` for which
`f` is close to `a` on a large portion of the circle of radius `r`. Values with positive
deficiency are attained less often than the First Main Theorem allows. -/
noncomputable def deficiency (f : ℂ → E) (a : WithTop E) : ℝ :=
  Filter.liminf (fun r ↦ proximity f a r / characteristic f ⊤ r) atTop

/-- The **truncated deficiency** `Θ(a)`, measuring both deficiency and ramification. -/
noncomputable def truncatedDeficiency (f : ℂ → E) (a : WithTop E) : ℝ :=
  1 - Filter.limsup (fun r ↦ truncatedLogCounting f a r / characteristic f ⊤ r) atTop
```

API, under the hypothesis `hT : Tendsto (characteristic f ⊤) atTop atTop` where needed:

```lean
theorem deficiency_nonneg / deficiency_le_one / truncatedDeficiency_nonneg /
        truncatedDeficiency_le_one
  -- 0 ≤ N̄/T ≤ N/T ≤ (T + C)/T eventually (combined FMT from package F), so the
  -- limsups lie in [0, 1 + ε] for all ε; boundedness side conditions from the same

theorem deficiency_le_truncatedDeficiency   -- δ(a) ≤ Θ(a)
  -- δ = liminf m/T = 1 − limsup N/T (FMT: m + N = T + O(1), T → ∞)
  --   ≤ 1 − limsup N̄/T = Θ   (N̄ ≤ N, package A)

theorem deficiency_eq_one_sub_limsup        -- the FMT bridge just used
theorem deficiency_eq_one_of_omits          -- omitted values have deficiency one (uses H's
                                            -- predicate or a divisor-vanishing hypothesis)

/-- Bridge: nonconstant meromorphic functions have unbounded characteristic. -/
theorem tendsto_characteristic_atTop_of_not_eventuallyConst {f : ℂ → ℂ}
    (hf : Meromorphic f) (h : ¬ EventuallyConst f (codiscrete ℂ)) :
    Tendsto (characteristic f ⊤) atTop atTop
  -- characteristic_isBigO_one_iff_constant (pending) + characteristic_monotoneOn:
  -- monotone and not bounded ⟹ tends to ∞
```

**The defect relation** (S3 as in §1) and corollary `sum_deficiency_le`. Proof sketch:

1. Transcendence `h : Real.log =o[atTop] characteristic f ⊤` gives
   `Tendsto (characteristic f ⊤) atTop atTop` (since `log r → ∞`) and in particular
   eventual positivity of `T`.
2. From S2 obtain `c` and the eventual inequality along `F := volume.cofinite ⊓ atTop`.
   Divide by `T r` (eventually positive):
   `(#S − 2 : ℝ) ≤ ∑ a ∈ S, N̄(r,a)/T r + c · (log⁺ (T r) + log r)/T r` along `F`.
3. The error tends to `0` along `F`: `log⁺ (T r)/T r → 0` (`Real.isLittleO_log_id_atTop`
   composed with `T → atTop`, restricted to the finer filter), and `log r/T r → 0` is the
   transcendence hypothesis (restricted via `IsLittleO.mono`, `F ≤ atTop`).
4. `NeBot F` (small standalone lemma: any `[a, ∞)` minus a finite-measure set has infinite
   measure, hence is nonempty). Take `limsup` along `F`:
   `(#S − 2 : ℝ) ≤ limsup_F (∑ a, N̄(·,a)/T) ≤ ∑ a, limsup_F (N̄(·,a)/T)`
   (finite subadditivity of `limsup`, by induction from `limsup_add_le`; boundedness side
   conditions from step "API" above).
5. Finer-filter comparison: `limsup_F u ≤ limsup_atTop u` for the bounded quotients
   (`F ≤ atTop`; `limsup_le_limsup_of_le` with coboundedness from nonnegativity).
6. Rearrange: `∑ a ∈ S, (1 − limsup_atTop (N̄(·,a)/T)) ≤ 2`, which is S3. The corollary
   for `δ` follows from `deficiency_le_truncatedDeficiency`.

Sanity check: `f = Complex.exp` omits `0` and `∞`, both defects are `1`, and S3 is sharp.

Estimated size: ~300 lines. Difficulty: medium (the mathematics is easy; `limsup/liminf`
side conditions — `IsBoundedUnder`/`IsCoboundedUnder` — are the fiddly part).

---

## 10. Work package H — Picard's little theorem (S4)

*Locally `VD/SMT/Picard.lean`; Mathlib target: new file `Analysis/Complex/Picard.lean`
(little Picard is **not** in Mathlib — only Picard–Lindelöf for ODEs — so this is a
flagship corollary). Depends on F (S2) and the pending
`rational_iff_characteristic_isBigO_log`.*

### H1. Filter-to-`atTop` transfer for monotone functions

```lean
/-- A monotone function bounded by `C · log` for large `r` outside a set of finite
measure is `O(log)` along `atTop` outright. -/
theorem MonotoneOn.isBigO_log_of_eventually_le {u : ℝ → ℝ} {x₀ C : ℝ}
    (h₁ : MonotoneOn u (Set.Ici x₀))
    (h₂ : ∀ᶠ r in volume.cofinite ⊓ atTop, u r ≤ C * Real.log r) :
    u =O[atTop] Real.log
```

Proof: extract from `h₂` a bad set `E` with `volume E =: M < ∞` and a threshold `R₀`. For
`r ≥ max R₀ (M + 2)`: the interval `[r, r + M + 1]` has measure `M + 1 > volume E`, so it
contains a good point `r′ ≥ r ≥ R₀`; then
`u r ≤ u r′ ≤ C · log r′ ≤ C · log (r + M + 1) ≤ 2C · log r`. Same measure-theoretic
device as the Borel lemma (`VD/MathlibSubmitted/BorelGrowth.lean`), but simpler — no
dyadic slicing. Reusable beyond Picard (any "monotone + exceptional set" cleanup); Mathlib
target near the Borel lemma.

### H2. The omission predicate and the three-value theorem

```lean
/-- `f` omits the value `a ∈ ℂ ∪ {∞}`, phrased through meromorphic orders (robust under
junk values): no poles for `a = ⊤`, no `a`-points otherwise. -/
def ValueDistribution.Omits (f : ℂ → ℂ) : WithTop ℂ → Prop
  | ⊤ => ∀ x, 0 ≤ meromorphicOrderAt f x
  | (a₀ : ℂ) => ∀ x, meromorphicOrderAt (f · - a₀) x ≤ 0

@[simp] lemma omits_top_iff / omits_coe_iff        -- definition unfolding
lemma Omits.of_forall_ne          -- for analytic f: (∀ z, f z ≠ a₀) → Omits f ↑a₀
lemma Omits.truncatedLogCounting_eq_zero          -- omitted ⟹ N̄(·, a) = 0
  -- the defining divisor vanishes: orders never positive resp. never negative

/-- **Picard's little theorem, meromorphic version**: a meromorphic function on `ℂ`
omitting three values of `ℂ ∪ {∞}` is constant away from a discrete set. -/
theorem ValueDistribution.eventuallyConst_of_omits {f : ℂ → ℂ} (hf : Meromorphic f)
    {S : Finset (WithTop ℂ)} (hcard : 3 ≤ S.card) (h : ∀ a ∈ S, Omits f a) :
    EventuallyConst f (codiscrete ℂ)
```

Proof route:
1. `Omits.truncatedLogCounting_eq_zero` kills the right side of S2:
   `∀ᶠ r in volume.cofinite ⊓ atTop, T r ≤ (S.card − 2)·T r ≤ c·(log⁺ (T r) + log r)`.
2. Absorption: eventually `c · log⁺ (T r) ≤ T r / 2` or `T r` is bounded (case split on
   `T r ≤ B₀` for the constant `B₀` with `c·log⁺ x ≤ x/2` for `x ≥ B₀`); either way
   `∀ᶠ r in volume.cofinite ⊓ atTop, T r ≤ 2c·log r + B₀`.
3. H1 (`characteristic_monotoneOn`): `characteristic f ⊤ =O[atTop] Real.log`.
4. `rational_iff_characteristic_isBigO_log` (pending):
   `f =ᶠ[codiscrete ℂ] p.eval / q.eval` with `q ≠ 0`.
5. Omission transfers along `=ᶠ[codiscrete ℂ]` (`divisor_congr_codiscreteWithin` /
   order-congruence), so `p.eval / q.eval` omits the three values as well.
6. **Algebraic finish** (standalone lemma, FTA): a rational function `p/q` omitting three
   values of `ℂ ∪ {∞}` is constant. If `p/q` omits `a₀ ∈ ℂ`, then `p − a₀·q` has no roots
   (accounting for cancellation via `gcd`-reduced representatives), hence is a nonzero
   constant by `Polynomial.exists_root`; two distinct finite omitted values force `q`
   constant (subtract: `(a₁ − a₂)·q = const`), i.e. `p/q` polynomial, and a nonconstant
   polynomial omits no finite value at all (FTA again) — while omitting `⊤` plus two
   finite values makes `p/q` a polynomial directly. Case-split bookkeeping on how many of
   the three values are `⊤` (at most one, `S` distinct).

### H3 = S4. Little Picard for entire functions

Statement as in §1. Proof: `f` differentiable ⟹ analytic (`Differentiable.analyticAt`) ⟹
`Meromorphic f` with all orders `≥ 0`, so `Omits f ⊤`; `ha`/`hb` give
`Omits f ↑a` / `Omits f ↑b` (`Omits.of_forall_ne`). Apply H2 with `S = {↑a, ↑b, ⊤}`
(card 3: `a ≠ b`, coercions ≠ `⊤`). From `EventuallyConst f (codiscrete ℂ)` obtain
`f =ᶠ[codiscrete ℂ] const c`; upgrade to equality everywhere by the identity theorem for
analytic functions (`f` and the constant agree on a set that clusters everywhere;
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` or continuity + density of
codiscrete sets).

Estimated size: H1 ≈ 60, H2 ≈ 160 (of which the algebraic finish ≈ 80), H3 ≈ 40; total
~280 lines. Difficulty: medium (H2's algebraic finish is elementary but case-heavy).

---

## 11. File layout and PR sequencing

All SMT work lives in the self-contained directory `VD/SMT/` (this plan included), one
local file per future Mathlib PR target, each registered by an import line in the root
`VD.lean`:

| # | Local file (`VD/SMT/`) | Mathlib target | Contents | Depends on |
|---|---|---|---|---|
| 1 | `TruncatedCounting.lean` | `Topology/LocallyFinsupp.lean` (extend) + **new** `…/ValueDistribution/LogCounting/Truncated.lean` | package A | — |
| 2 | `DivisorDeriv.lean` | **new** `Analysis/Meromorphic/DivisorDeriv.lean` | package B | 1 |
| 3 | `SeparationLemma.lean` | `Analysis/SpecialFunctions/Log/PosLog.lean` (extend) | package C | — |
| 4 | `ProximityEstimates.lean` | `…/ValueDistribution/SecondMainTheorem.lean` (part 1) | package D | 3, **LLD (T3)**, pending `CharacteristicMoebius` |
| 5 | `SecondMainTheoremRamification.lean` | `…/ValueDistribution/SecondMainTheorem.lean` (part 2) | package E (S1) | 4 |
| 6 | `SecondMainTheorem.lean` | `…/ValueDistribution/SecondMainTheorem.lean` (part 3) | package F (S2, S2′) | 1, 2, 5 |
| 7 | `Deficiency.lean` | **new** `…/ValueDistribution/Deficiency.lean` | package G (S3) | 6 |
| 8 | `Picard.lean` | **new** `Analysis/Complex/Picard.lean` | package H (S4) | 6, pending `CharacteristicIsBigOLog` |

- Items 1 and 3 are **fully parallel** and independently PR-able today; 2 follows 1.
- The **critical path** is 4 → 5 → 6 → {7, 8}, gated locally by nothing (the LLD is done)
  but gated *upstream* by the LLD PR chain (PoissonJensen → LogDerivTwoRadius →
  LogDerivLemma); schedule PRs 1–3 while that chain is in review.
- Every PR stays under ~400 lines. New Mathlib files must use the module system
  (`module` / `public import` / `@[expose] public section`) as in the current
  ValueDistribution files; the local VD copies can stay in classic mode until upstreaming.
- Doc-string style: follow `FirstMainTheorem.lean` (references to [MR886677] Ch. VII and
  [MR3156076]; quantitative statement with explicit constant + qualitative corollary).

Total new code estimate: ≈ 2200–2500 lines of Lean.

## 12. Risks and fallbacks

1. **Separation-lemma case analysis (C).** Elementary but easy to over-engineer.
   Mitigation: existential constant (zero pressure on sharpness), normalize `δ ≤ 1` from
   the start, treat `w = a₀` via Lean's `(0 : ℝ)⁻¹ = 0` (the statement then holds for
   *all* `w`, so D4's integration step needs no codiscrete comparison at all). Fallback:
   prove it over `ℂ` only if `NontriviallyNormedField` generality causes friction.
2. **Junk values around `1/f′` and `logDeriv` (D3/D4).** All function identities are
   asserted only `=ᶠ[codiscrete ℂ]` and consumed through `proximity_congr_codiscrete`
   (`r ≠ 0` — eventually true) — the LLD discipline. The pointwise identity in D4 step 3
   was checked to survive Lean's `x/0 = 0` even at points with `f z = a`.
3. **The constancy dichotomy D1** is the one genuinely delicate proof (normal-form
   transfer + identity theorem). Fallback: state S1/S2 first with the hypothesis
   `∀ x, meromorphicOrderAt (deriv f) x ≠ ⊤` and add the hypothesis-free wrappers in a
   follow-up — the package structure supports this (D1 is isolated). Like the LLD's T1,
   it depends on the *pending* `CharacteristicMoebius` chain — no new upstream exposure.
4. **`WithTop ℤ` order arithmetic in B** (`untop₀`, three-way case splits) is mechanical
   but verbose. Mitigation: mirror the LLD order-section style; keep every divisor
   identity pointwise-first, then lift with `locallyFinsuppWithin` extensionality.
5. **`limsup`/`liminf` side conditions in G.** `IsBoundedUnder`/`IsCoboundedUnder` goals
   accompany every `limsup` manipulation over `ℝ`. Mitigation: all quotients here are
   eventually in `[0, 2]` (combined FMT), so a small private "bounded quotient" helper
   discharges them uniformly. The `NeBot (volume.cofinite ⊓ atTop)` lemma and the
   finite-subadditivity of `limsup` over a `Finset` are small standalone pieces, both
   Mathlib-worthy.
6. **Defect relation for rational `f`** is genuinely out of reach of this error term —
   scoped out by design decision 8 and noted as a follow-up (§13).
7. **Private LLD helpers.** `circleAverage_mono_codiscreteWithin` (private in
   `LogDerivTwoRadius.lean`) is *not* expected to be needed (see risk 1); if a
   codiscrete-only comparison does surface, re-expose it as a public lemma (it is
   Mathlib-worthy anyway).
8. **`Finset (WithTop ℂ)` plumbing in F** (`Finset.preimage` along
   `WithTop.coe_injective`, sum splitting). Bounded annoyance. Fallback: prove an
   auxiliary version taking `(s : Finset ℂ)` plus a Boolean "count `⊤`" flag and derive
   the `WithTop` statement from it.
9. **The algebraic finish of H2** (rational function omitting three values) is elementary
   but case-heavy; watch for cancellation between `p` and `q` (use coprime/`gcd`-reduced
   representatives, or argue with `divisor` directly, where cancellation is invisible).
10. **Upstream latency.** PRs 4–8 cannot land before the LLD chain; PRs 1–3 are
    independent — front-load them. Naming (`trunc`, `truncatedLogCounting`,
    `secondMainTheorem`, `Omits`) may get bikeshedded; nothing downstream depends on it.

## 13. Milestones

1. **M0**: this plan + eight comment-only stub files compile green (registered in
   `VD.lean`).
2. **M1** (parallel): packages A and C compile; then B. Each individually PR-able
   (A and C immediately).
3. **M2**: package D — the `S(r)` lemmas. D2 is already a citable statement
   ("the LLD for arbitrary finite targets").
4. **M3**: S1 (ramification form) proved — the mathematically complete SMT.
5. **M4**: S2 + posPart corollaries + sanity examples; upstream PRs 4–6 once the LLD
   chain has landed.
6. **M5**: deficiencies + the defect relation S3.
7. **M6**: Picard S4 (meromorphic three-value version + entire version).
8. **Post-SMT** (out of scope, next plan): Nevanlinna's five-value theorem (via `Omits`
   and shared-value counting); the defect relation for rational functions (algebraic);
   explicit-constant/two-radius SMT refinement (Lang–Cherry); level-`k` truncated
   counting `N_k` and the corresponding defect inequalities.
