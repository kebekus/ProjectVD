# Jireh Loreaux Review Rulebook

Distilled from **324 review comments across 46 of Stefan Kebekus's mathlib PRs**
(reviewer `j-loreaux`), harvested 2026-07. This is the authoritative catalog that
the `autoJireh` skill checks against. Each rule has: how to **detect** it, the
**fix**, and an auto-apply **confidence**:

- **MECHANICAL** — safe to auto-fix (formatting, spacing, typos, within-file string swaps).
- **SEMI** — auto-fix then verify with `lake build`; revert if it breaks. Often needs a small proof tweak or call-site update.
- **JUDGMENT** — naming/design/API decisions. Do **not** silently edit: report it in Jireh's voice with a proposed diff and let the human decide.

---

## 1. Naming conventions

### 1.1 `eventuallyLE`/`eventuallyLT`/`eventuallyEq`, not `eventually_le` — SEMI
- **Detect:** a name containing `_eventually_le`/`_eventually_lt`/`_eventually_eq` whose statement uses `≤ᶠ[…]`, `<ᶠ[…]`, `=ᶠ[…]`.
- **Fix:** `counting_top_add_eventually_le` → `counting_top_add_eventuallyLE`. ("This is how we refer to `≤ᶠ[filter]`.") String rename + update call sites. (PR 31581)

### 1.2 Primes `'` to distinguish similar decls, never subscripts `₁`/`₂` — JUDGMENT
- **Detect:** declaration names ending in a digit subscript `₁ ₂ …`.
- **Fix:** `…_off_countable₁` → `…'`, but "more informative names are always better" — prefer a descriptive rename. (PR 34458, 34482)

### 1.3 `_fun` marks the pointwise/lambda variant, immediately before the operation — JUDGMENT/SEMI
- **Detect:** `add_fun`, `fun_iteratedFDerivWithin_sum_apply`, or a hand-written `fun z ↦ f z + g z` lemma.
- **Fix:** `circleAverage_add_fun` → `circleAverage_fun_add`. If the target name is already taken, rename the pre-existing one (in a separate PR). (PR 31556, 36214)

### 1.4 Zero-function naming: `_zero` = applied, `_fun_zero` = eta-expanded — SEMI
- **Detect:** `_zero_fun`, `iteratedFDeriv_zero_fun`.
- **Fix:** `iteratedFDerivWithin_zero_fun` → `iteratedFDerivWithin_zero`; eta-expanded variant → `iteratedFDerivWithin_fun_zero`. Delete "Eta-expanded version…" docstrings once renamed. (PR 36214)

### 1.5 Name component order must match the statement (`_add_top`, not `_top_add`) — JUDGMENT
- **Detect:** operation/eval-point tokens out of statement order.
- **Fix:** `proximity_top_add_le` → `proximity_add_top_le`; `proximity_top_sum_le` → `proximity_sum_top_le`. (PR 31556, 31581)

### 1.6 `_of_top` (adding a top-order function) not `_top` (adding literal `⊤`) — JUDGMENT
- **Detect:** `_add_top_left`/`_add_top_right` where nothing literally `⊤` is added.
- **Fix:** `meromorphicOrderAt_add_top_left` → `meromorphicOrderAt_add_of_top_left`. ("since you aren't really adding `⊤`.") (PR 31581)

### 1.7 Hypotheses go at the end via `_of_…` — JUDGMENT
- **Detect:** a hypothesis token appears before the subject or as a bare suffix.
- **Fix:** `continuousOn_smul` → `smul_of_continuousOn`; `mem_codiscreteWithin_subsingleton` → `mem_codiscreteWithin_of_subsingleton`; `divisor_subset_finiteSupport` → `divisor_support_finite_of_subset`. (PR 38581, 39566, 40191, 37477)

### 1.8 Sign/order conditions: `lt_zero`/`pos`/`eq_zero`, never `neg` — JUDGMENT
- **Detect:** `_neg_`/`_pos_`/`_zero_` naming an order/sign condition, especially `neg`.
- **Fix:** `…_of_neg_meromorphicOrderAt` → `…_of_meromorphicOrderAt_lt_zero` ("We don't use `neg` so it doesn't get confused with `-`"); `_of_pos_…` → `_of_meromorphicOrderAt_pos`; `_of_zero_…` → `_of_meromorphicOrderAt_eq_zero`. (PR 38581)

### 1.9 Use the full/correct head symbol matching the real declaration — JUDGMENT/SEMI
- **Detect:** name uses a shortened or wrong concept vs. the statement.
- **Fix:** `counting_*` → `logCounting_*`; `logCounting_const_zero` → `logCounting_zero`; use the real decl name (`meromorphicTrailingCoeffAt`). Public lemmas "should definitely use the full name." (PR 31053, 31581, 32311, 38581)

### 1.10 `_iff` lemmas: `X_eq_zero_iff`, not `zero_X_iff`; orient the `↔` naturally — JUDGMENT
- **Detect:** `zero_<thing>_iff`, or an `↔` whose name reads backwards.
- **Fix:** `zero_canonicalFactor_iff` → `canonicalFactor_eq_zero_iff`; turn `meromorphicAt_iff_meromorphicAt_add` around so the hypothesis side is natural. (PR 31262, 37477)

### 1.11 Name direction must match the equality's direction — JUDGMENT
- **Detect:** `X_eq_Y` whose statement is `Y = X`. Fix: flip statement or rename. (PR 38500)

### 1.12 Property spelled out: `_support_finite`, not `_finiteSupport` — JUDGMENT
- **Fix:** `divisor_sphere_finiteSupport` → `divisor_sphere_support_finite`. (PR 37477)

### 1.13 Evaluation lemma is `_apply`, not `_eval`; `_apply_self` at the defining point — JUDGMENT
- **Fix:** `single_eval` → `single_apply`; `canonicalFactor_eval_center` → `canonicalFactor_apply_self`. (PR 34919, 36264)

### 1.14 Defs are lowerCamelCase; namespace ℂ-specific defs in `Complex` — JUDGMENT
- **Detect:** a `def`/`noncomputable def` with an UpperCamelCase name (not a type/Prop); ℂ-specific decls outside `Complex`.
- **Fix:** `CanonicalFactor` → `canonicalFactor`; `Poisson` → `poisson`; put them in `Complex`. (PR 35399, 36264)

### 1.15 Avoid overly generic def names — JUDGMENT
- **Fix:** `poisson` → `poissonKernel`. If a concept appears in a lemma name but nowhere in its statement, introduce a bespoke def. (PR 35399)

### 1.16 No `aux` in a name unless the decl is `private` — JUDGMENT
- **Fix:** make it `private`, or drop `aux` and give a real name. (PR 35399, 36264)

### 1.17 Structure fields drop the subject prefix — SEMI
- **Fix:** `f_meromorphicOn` → `meromorphicOn`; `g_ne_zero` → `ne_zero`. (PR 37477)

### 1.18 Namespace for dot notation; subject type's namespace first — JUDGMENT/SEMI
- **Detect:** a lemma about `IsOpen`/`HarmonicOnNhd`/etc. not in that namespace; `Subject.foo_of_bar` where `Bar.foo` gives dot notation.
- **Fix:** `PerfectSpace.preperfect_of_isOpen` → `IsOpen.preperfect`. "Trying to use dot notation uncovered an error in naming!" (PR 36278, 37371, 33889)

### 1.19 Lowercase proper nouns mid-name — JUDGMENT
- **Fix:** `countable_of_Lindelof_of_discrete` — "the `L` should be lower case." (PR 32675)

### 1.20 Deprecation aliases must target the actual new name — SEMI
- **Fix:** point `@[deprecated] alias old := new` at the correct renamed decl; move pre-existing renames into a separate PR with deprecations (script in `scripts/`). (PR 36214, 31581)

---

## 2. `Set.univ` / `∈ univ` / `⊤` handling

### 2.1 Omit `∈ univ` — SEMI
- **Detect:** `∀ z ∈ univ, P z` / `∀ z ∈ Set.univ, …`.
- **Fix:** `(h : ∀ z ∈ univ, meromorphicOrderAt f z ≠ ⊤)` → `(h : ∀ z, meromorphicOrderAt f z ≠ ⊤)`. "This will require fixing the proof ever so slightly." Applies throughout. (PR 30494)

### 2.2 Prefer `Set.univ` over `⊤` for sets — SEMI
- **Detect:** `⊤ : Set X`, `top_eq_univ`, `univ_mem` reached via `⊤`. "generally it's better to use `Set.univ` instead of `⊤` for sets." (PR 34919)

### 2.3 Repeated `MeromorphicOn f Set.univ` is a design smell — JUDGMENT
- **Fix:** open a Zulip thread for a `Meromorphic f := MeromorphicOn f Set.univ` predicate (like `Continuous`/`ContinuousOn`/`ContinuousAt`). Until then, name a general `… ∩ U` lemma `…_inter` + a `univ` convenience lemma. In a bare theorem in the `MeromorphicOn` namespace prefer `theorem measurable …` over `theorem meromorphic_measurable …`. (PR 30494, 31581, 32675)

### 2.4 Don't add `…_meromorphicOn_univ` convenience lemmas — JUDGMENT
- **Fix:** drop them; use `Meromorphic.meromorphicOn` / supply the implicit. (PR 33152)

---

## 3. Proof style & tactics

### 3.1 `gcongr` for monotonicity/congruence of inequalities — SEMI
- **Detect:** `apply add_le_add`, `mul_le_mul_*`, `div_le_div_*`, chains of `le_trans`, componentwise case splits.
- **Fix:** replace with `gcongr`. "This isn't just to golf. I want to make sure you know about the existence of this tactic." Also tag your own monotonicity lemmas `@[gcongr]`. (PR 33704, 30494, 35399)

### 3.2 `grw` to rewrite through inequalities — SEMI
- **Fix:** `grw [norm_add_le, ← norm_sub_norm_le]` instead of manual `le_trans`/`calc` rewrites. (PR 36938)

### 3.3 Existing library lemmas over ad-hoc `have … := by ring; rw` — SEMI
- **Detect:** a local `have {A B C D : ℝ} : … := by ring` then `rw [this]`.
- **Fix:** `rw [add_add_add_comm]`. Search for the named lemma. (PR 30494)

### 3.4 `simpa [...] using e` over `simp only [...]; exact e` — SEMI
- **Detect:** `simp only [...]` (or `simp`) on its own line, then `exact …`.
- **Fix:** `simpa only [characteristic, Pi.add_apply] using add_nonneg …`. If the simp only applies defeqs, drop it entirely and give the term (`:= add_nonneg …`, no `by`). "`simpa` is helpful when you want to construct a term, but both that term and/or the goal need to be simplified before they match." (PR 33889, 36938, 37477)

### 3.5 Non-terminal `simp`/`norm_num` is a smell; state intermediate goals — JUDGMENT
- **Detect:** `norm_num [...]` mid-proof (it silently calls `simp`), back-to-back `simp`, `simp; …; rw; ring` chains.
- **Fix:** insert a `suffices`/`calc` giving simp an explicit target (`simp + ring` at the very end is fine). (PR 35399, 36938)

### 3.6 `calc` blocks for readability and to pin the goal — SEMI
- **Detect:** repeated `.trans`/`le_trans`, or one long `rw` doing everything.
- **Fix:** rewrite as a `calc` (optionally with `grw`). "calc blocks tell Lean exactly what the goal is [and] improve readability." (PR 36938, 35399, 41496)

### 3.7 `suffices` for the natural intermediate step — SEMI
- **Fix:** `suffices ∀ z, 0 ≤ …`; `suffices ∀ z w, exp (F z) = exp (F w) by grind`. (PR 35399, 35640, 36938)

### 3.8 Terminal tactic in a sequence: `exact`, not `apply` — SEMI
- **Detect:** a bullet/sequence ending in `apply foo` that closes the goal.
- **Fix:** `apply meromorphicNFAt_prod …` → `exact meromorphicNFAt_prod …`. "We generally end terminal tactics within a sequence with `exact` instead of `apply`." (PR 36597, 36938)

### 3.9 `refine … ?_` over `apply … _`; name the holes — SEMI
- **Detect:** `apply foo _ _`; unnamed `?_` where order matters.
- **Fix:** `refine foo (U := …) … ?_`; named holes `?meas ?int` with `case meas => …`. "when `apply` uses `_`, it's not clear whether Lean can infer the underscore or whether that's the argument being supplied." (PR 40191, 37477, 41952, 41496)

### 3.10 Introduce variables inline in `refine`/`apply` — SEMI
- **Detect:** `apply foo` then `intro x hx`.
- **Fix:** `apply circleAverage_congr_sphere fun z hz ↦ ?_`. You can also bind vars in `have (z) (hz : z ∈ U) : … := …`. (PR 34482, 37477, 38581, 36597)

### 3.11 `by_cases!` combines `by_cases` + `rw [not_not]`; `by_contra!` — SEMI
- **Fix:** `by_cases! hz : z ∉ U`; `by_contra! hInf`. (PR 32311, 40957)

### 3.12 `obtain (rfl | h) := eq_or_ne …` over `by_cases` + `subst` — SEMI
- **Fix:** `obtain (rfl | h₂z) := eq_or_ne z w`. (PR 37477, 35399, 36264)

### 3.13 Don't squeeze `grind`/`simp` without a reason — SEMI
- **Fix:** `grind only [ne_of_mem_sphere, …]` → `grind [ne_of_mem_sphere]`. "we probably don't want to squeeze `grind` calls without a reason (for the same reason we don't squeeze `simp`)." (PR 34482)

### 3.14 Feed `grind` the right lemmas over manual arithmetic — SEMI
- **Fix:** `grind [logCounting_le, log_nonneg, logCounting_nonneg]`. (PR 35399, 36597, 40957, 41952)

### 3.15 `positivity` (with the right scope open) over manual nonneg/pos chains — SEMI
- **Detect:** `apply mul_nonneg …; apply add_nonneg …`, `div_pos …`, `integral_nonneg fun …`.
- **Fix:** `positivity`. For ℂ, `open scoped ComplexOrder in`. (PR 35399, 38500, 36264)

### 3.16 Avoid unnecessary case splits with careful lemma/inequality choice — SEMI
- **Fix:** e.g. `rw [← circleAverage_abs_radius]; exact … (by simpa) …`. "If you're just slightly more careful with your inequalities, you can avoid the case split." (PR 30494, 34482, 35399, 36938)

### 3.17 `filter_upwards` one-liner `with … using …` — SEMI
- **Detect:** `filter_upwards [...]` then `exact fun _ hr ↦ …`.
- **Fix:** `filter_upwards [Filter.eventually_ge_atTop 1] with r hr using foo …`. (PR 33704, 36938)

### 3.18 `conv_lhs`/`conv_rhs` over `conv => left/right` — MECHANICAL
- **Fix:** `conv => right; …` → `conv_rhs => …`. (PR 37477)

### 3.19 Define functions point-fully to avoid beta reduction — JUDGMENT
- **Fix:** `def herglotzRiesz (c w z : ℂ) : ℂ := …` instead of `:= fun z ↦ …`. (PR 35399)

### 3.20 `convert`/`congr! n` over hand-massaging subterms — SEMI
- **Fix:** `convert foo using 1`; `congr! 1; ring`. (PR 35399, 40696, 41496)

### 3.21 Combine identical branches with `all_goals`/`<;>` — SEMI
- **Fix:** `all_goals simpa [h] using locallyFinsuppWithin.logCounting_mono (by positivity)`. (PR 33889, 30494)

### 3.22 Restructure statements to enable `fun_prop`/`aesop`; give Lean type info — JUDGMENT
- **Fix:** e.g. `DifferentiableOn.diffContOnCl` to turn a goal into `fun_prop`; factor a `have`/`calc` to avoid a large `simp only`. (PR 35399, 35640)

---

## 4. Attributes

### 4.1 `protected` when a name shadows a root decl — SEMI
- **Detect:** a lemma named `deriv`/`measurable`/etc. in a namespace + later `_root_.deriv` disambiguation.
- **Fix:** `protected theorem deriv …` removes the need for `_root_.deriv`. (PR 32385, 33117)

### 4.2 Don't `@[simp]` when it forces simp to discharge side goals — JUDGMENT
- **Detect:** `@[simp]` on a lemma with a hypothesis like `0 < n`, `Set.Finite s`, or a non-canonical LHS.
- **Fix:** drop `@[simp]`. "it makes `simp` try to solve `0 < n` as a side goal." (PR 36214, 38581, 36673)

### 4.3 `@[to_fun]` to auto-generate the pointwise (`_fun_`) variant — SEMI
- **Fix:** tag the base lemma `@[to_fun]` (or `@[to_fun (attr := simp)]`) and delete the manual copy. Verify the generated name with `@[to_fun?]`, hovering, or `whatsnew in`. (PR 35256, 36214, 40533)

### 4.4 `@[fun_prop]` only on genuine transition theorems — JUDGMENT
- **Detect:** `@[fun_prop]` where the base predicate isn't itself `fun_prop`; asymmetric tagging.
- **Fix:** remove it; if the base predicate should be tagged, do it in a separate PR with Zulip buy-in. (PR 35564)

### 4.5 `@[pp_nodot]` on a def meant to display with dot notation — JUDGMENT
- **Fix:** `@[pp_nodot] noncomputable def posLog …`. (PR 23628)

### 4.6 Don't `@[expose]` a def; use its `_def` lemma — JUDGMENT
- **Fix:** use `herglotzRieszKernel_def`; revert unexplained `@[expose] public section` to reduce diff. (PR 32675, 36278)

### 4.7 `@[grind]` naming still follows `_of_` — JUDGMENT
- **Fix:** `re_eq_re_if_cexp_eq_cexp` → `re_eq_re_of_cexp_eq_cexp` (`_if_` → `_of_`). (PR 35640)

---

## 5. Formatting & indentation

### 5.1 Signature continuation lines indent 4 spaces — MECHANICAL
- **Detect:** a hypothesis/continuation line under `theorem`/`lemma` indented only 2 spaces.
- **Fix:** `  (hf₂ : CircleIntegrable f₂ c R) :` → `    (hf₂ : CircleIntegrable f₂ c R) :`. (PR 31556, 31581, 31583 — flagged 10+ times)

### 5.2 `calc`: following lines indent +2; justifications indent further — MECHANICAL
```
calc proximity (f₁ + f₂) ⊤ r + …
  _ ≤ (proximity f₁ ⊤ r + …) := by
    …
```
"The lines following a `calc` should be indented by two spaces … it fits with Lean's general rule of 'indent blocked code'." (PR 33704, 31556, 31581)

### 5.3 Don't split code fragments across lines in docstrings — MECHANICAL
- **Detect:** an inline `` `f₁ + f₂` `` broken over a line wrap. Keep it intact; rewrap surrounding prose. (PR 31262)

### 5.4 Spacing hygiene — MECHANICAL
- `¬MeromorphicAt` → `¬ MeromorphicAt`; `hf: T` → `hf : T`; `h₂a,circleMap` → `h₂a, circleMap`; `[ mul_pos … ]` → `[mul_pos …]`. (PR 38581, 36278, 35399)

### 5.5 No blank lines between struct fields; one blank line before a top-level lemma — MECHANICAL
- "We generally don't insert blank lines between fields of a structure." (PR 40191, 36673)

### 5.6 Leading-dot `|>.` continuation for long chains — MECHANICAL
- `… hw).differentiableAt.differentiableWithinAt` → break with `…\n    |>.differentiableAt.differentiableWithinAt`. (PR 41952, 40696)

---

## 6. Documentation & docstrings

### 6.1 Fix typos — MECHANICAL
- Flagged: "non-trival", "Titerated", "supporty", "on will", "analytin". (PR 38581, 36214, 40957, 36264, 40191)

### 6.2 Common nouns lowercase in prose — MECHANICAL
- "Complex Analysis" → "complex analysis." (PR 31583)

### 6.3 Italics for defined terms; backticks only for code — JUDGMENT (light)
- `` `Canonical Decomposition` `` → *Canonical Decomposition*. (PR 36264)

### 6.4 Disambiguate `Finset.sum` in docstrings — MECHANICAL
- `∑ a, f a` → `∑ a ∈ s, f a`. (PR 31581)

### 6.5 Docstring must describe the actual statement/concept — JUDGMENT
- "counting" → "characteristic" where the function is `characteristic`; "Derivatives" → "Iterated derivatives" for iterated lemmas. (PR 31053, 36597, 32385, 38984, 37477)

### 6.6 Explain constants/non-obvious conditions — JUDGMENT
- State that `log 2` comes from two summands / `log s.card` for `s.card` summands; explain "no poles" = `MeromorphicNFOn g ∧ g ≠ 0`. (PR 31556, 33704, 37477, 40696)

### 6.7 Add cross-references between related theorems — JUDGMENT
- "See `MeromorphicOn.circleAverage_log_norm` for Jensen's formula in the original context" (+ the reverse link). (PR 31583)

### 6.8 Docstring variable names must match the definition — MECHANICAL
- Docstring `g` vs definition `h` — pick one. (PR 40191)

### 6.9 Outline long proofs with comments — JUDGMENT
- Add step comments to giant `rw`/many-step proofs. (PR 40191, 37477)

### 6.10 Document literature errors / counterexamples in module docs — JUDGMENT
- A hypothesis that silently fixes a mistake in the literature: document the error + counterexample. "it may not be documented anywhere else at all!" (PR 30494)

### 6.11 Cite the bibliography file, don't inline references — JUDGMENT (PR 38581)

### 6.12 Delete now-pointless "deviating from naming convention" docstrings after a rename — SEMI (PR 36214)

---

## 7. API / design

### 7.1 Unfolding an instance/def in `rw` means a missing/misused API lemma — JUDGMENT/SEMI
- **Detect:** `rw [instPosPart, …]`, `unfold Foo`, `simp [Foo]` where `Foo` is a def.
- **Fix:** add/use the proper lemma: `rw [posPart_def]`, `rw [negPart_def]`, `rw [canonicalFactor_def]`. "`rw [instPosPart …]` suggests we're missing a lemma … Please add the lemma you need." (PR 30494, 36278)

### 7.2 Add symmetric / turned-around variants — JUDGMENT
- Add the `+`-symmetric and the `g`-hypothesis variant; `Meromorphic.congr_codiscrete` + `meromorphic_congr_codiscrete` alongside the `On` version. (PR 31262, 34302)

### 7.3 Add `sub`/`sum`/`^ℕ` companions to `add`/`^ℤ` — JUDGMENT
- Add `circleAverage_fun_sub`, `circleAverage_fun_sum`; add the `n : ℕ` power version. (PR 31556, 35689, 34919)

### 7.4 Add the genuinely missing base lemma instead of working around it — JUDGMENT
- A proof "working too hard" that duplicates something provable from a `Pi.*`/`WithTop.*`/`Function.*` lemma that doesn't yet exist: add the base lemma (`coe_single`, `Pi.single_pos`, `WithTop.untop₀_one`, `conj_circleMap`, a `positivity` extension, `@[fun_prop] Measurable.posPart/negPart`). When a proof deviates from the paper proof, ask why — usually "missing API" (add it) or "missing automation" (tag `@[simp]`). (PR 34919, 37477, 40664, 36938, 38500, 41496)

### 7.5 Generalize instead of special-casing — JUDGMENT
- `single x` with an arbitrary value `n`, not fixed `1`; Liouville over a finite-dim inner product space, not `ℝ`; prove the general lemma first, then derive the special case. (PR 34919, 35640, 40664, 40533, 32385, 38581)

### 7.6 Follow existing design patterns (`Finsupp.single`, `Pi.single`) — JUDGMENT
- Use `Classical.decEq` in the definition but take a `Decidable` argument in the expansion lemma (`single_apply`), mirroring `Finsupp.single`. (PR 34919)

### 7.7 Use dot notation wherever possible — SEMI
- `Function.Even.add proximity_even logCounting_even` → `proximity_even.add logCounting_even`; `Function.Even (characteristic f a)` → `(characteristic f a).Even`. Missing dot notation often signals a namespacing error. (PR 33889, 36938, 36278, 37477)

### 7.8 Prefer `/` over `* ⁻¹` — JUDGMENT
- `(z - w)⁻¹ • …` → `((z - c) / (z - w)) • …`. "here and throughout, I think we would normally write it this way." (PR 34482, 41817)

### 7.9 Add `sub` versions of lemmas rather than `by rfl` sub↔add casts — JUDGMENT
- Repeated `(by rfl : (f · - a) = f + (fun _ ↦ -a))`: add `…_sub_…` variants instead. (PR 38581, 40533)

### 7.10 Right `private` calibration — JUDGMENT
- Unmark `private` on reasonable public statements; mark genuinely odd helpers `private` (and then don't use `aux`). "aside from the name, I don't see any reason this should be `private`." (PR 38500, 36264, 35399)

### 7.11 Prefer a `structure` (+ dot notation) for compound concepts; make it `Prop` — JUDGMENT
- `∃ g, P ∧ Q ∧ R` → `structure CanonicalDecomp … : Prop where …`; `: Prop` avoids a universe bump. (PR 37477, 40191)

### 7.12 Reuse existing library lemmas instead of reproving — SEMI
- `Set.Subsingleton.eq_empty_or_singleton`; `Pi.support_single_of_ne`; `Integrable.pos_part`; `Function.Even.const`; `WithTop.untop₀_natCast`. (PR 36597, 34919, 38500, 40664, 40957)

---

## 8. Notation & scoping / `open`

### 8.1 Keep notation scoped — JUDGMENT
- `notation "log⁺" => posLog` → `scoped notation …`, scoped to `Real`. (PR 23628)

### 8.2 Open the scope a tactic needs — SEMI
- `open scoped ComplexOrder in` for `positivity` on ℂ; `open scoped Pointwise` for `+ᵥ`/`- {c}`. (PR 36264, 40533)

### 8.3 `open … in` to strip namespace clutter; reuse already-open namespaces — SEMI
- `open Finset in` / `open Complex in`; drop explicit `volume` (`MeasureTheory` already open). (PR 36597, 36938, 35640)

---

## 9. PR process / meta (report as advice; never auto-edit)

### 9.1 Separate renames (with deprecations) from feature PRs — JUDGMENT
- Name new lemmas correctly here; move pre-existing renames + `@[deprecated]` aliases into a dedicated PR (use `scripts/`; keep the diff minimal). "As it stands, we have the worst of both worlds." (PR 31581)

### 9.2 Don't open a fresh PR when one goes sideways — JUDGMENT
- Keep working in the same PR to preserve comment history. (PR 32311)

### 9.3 Take design decisions to Zulip — JUDGMENT
- New core predicate, tagging a predicate family `fun_prop`, `⁻¹` vs negative power, generalizations: open/point to a Zulip thread first. (PR 30494, 31581, 35564, 41817)

### 9.4 Minimize the diff / split code movement — JUDGMENT
- Revert unrelated changes (`@[expose] public section`, `open` reordering); split pure code movement into its own PR. (PR 24845, 32675)

### 9.5 Split large auxiliary API into its own PR — JUDGMENT (PR 38500, 35564)

---

## Auto-fix priority (highest-value, lowest-risk first)

1. **MECHANICAL formatting/prose:** 5.1 signature indent · 5.2 calc indent · 5.4 spacing · 5.5 struct blank lines · 5.3 docstring code splits · 6.1 typos · 6.2 lowercase · 6.4 `∑ a ∈ s` · 6.8 doc var names · 3.18 `conv_rhs`.
2. **SEMI tactic rewrites (compile-check each):** 3.4 `simpa … using` · 3.8 terminal `exact` · 3.11 `by_cases!` · 3.12 `eq_or_ne` · 3.15 `positivity` · 3.1 `gcongr` · 3.13 un-squeeze · 2.1 omit `∈ univ` · 2.2 `⊤`→`Set.univ` · 4.1 `protected`.
3. **JUDGMENT (propose, don't auto-apply):** all of §1.5–1.19 semantic naming · §2.3 `Meromorphic` predicate · §4.2/4.4 attribute appropriateness · §7 API/design · every §9 process rule.
