/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import VD.MathlibPending.CharacteristicIsBigOLog
import VD.SMT.SecondMainTheorem

/-!
# Picard's Little Theorem — SMT work package H

See `VD/SMT/PLAN-SecondMainTheorem.md`, §10.

Mathlib target: new file `Mathlib/Analysis/Complex/Picard.lean` (Picard's little theorem
is currently absent from Mathlib).
Dependencies: `VD/SMT/SecondMainTheorem.lean` (package F) and the pending
`VD/MathlibPending/CharacteristicIsBigOLog.lean` (characterization of rational functions
by characteristic growth).

## Main results

- H1, `MonotoneOn.isBigO_log_of_eventually_le`: filter-to-`atTop` transfer — a monotone
  function bounded by `C · log` for large `r` outside a set of finite measure is `O(log)`
  along `atTop` outright.  (Same measure-theoretic device as the Borel growth lemma in
  `Mathlib/MeasureTheory/Function/BorelGrowth.lean`, but simpler.)

- H2, `ValueDistribution.Omits`: the omission predicate for values in `ℂ ∪ {∞}`, phrased
  through meromorphic orders (robust under junk values), with the bridge lemmas
  `Omits.of_forall_ne`, `Omits.congr` and `Omits.truncatedLogCounting_eq_zero`; then
  `ValueDistribution.eventuallyConst_of_omits`: **Picard's little theorem, meromorphic
  version** — a meromorphic function on `ℂ` omitting three values of `ℂ ∪ {∞}` is
  constant away from a discrete set.

- H3, `Differentiable.exists_eq_const_of_forall_ne`: **Picard's little theorem, entire
  version** — an entire function omitting two finite values is constant.

The proof of H2 combines the Second Main Theorem with the growth characterization of
rational functions: since all truncated counting functions of omitted values vanish, the
Second Main Theorem forces `T(r, f) = O(log⁺ T(r, f) + log r)` outside a set of finite
measure; absorbing the `log⁺ T` term and applying H1 gives `T(r, f) = O(log r)`, so `f`
is rational.  A rational function `p/q` omitting two distinct finite values `a ≠ b` is
constant by the fundamental theorem of algebra: with `p`, `q` coprime, both `p − a·q` and
`p − b·q` are root-free, hence constant, and subtracting shows that `q` and `p` are
constant.  (Since at most one of the three omitted values is `∞`, two distinct finite
omitted values always exist.)

References: [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677], Ch. VII, §3;
[Hayman, *Meromorphic Functions*][MR164038], §2.5.
-/

open Asymptotics Filter Function MeasureTheory Metric Real Set Topology

/-!
## Filter-to-`atTop` Transfer for Monotone Functions

The Second Main Theorem provides estimates for all large radii *outside a set of finite
Lebesgue measure*.  For monotone functions — such as the Nevanlinna characteristic — the
exceptional set can be removed: any interval of length exceeding the measure of the
exceptional set contains a good radius, and monotonicity transfers its estimate.
-/

/--
A function that is monotone on `[x₀, ∞)` and bounded by `C · log` for all large radii
outside a set of finite Lebesgue measure is `O(log)` along `atTop` outright.
-/
theorem MonotoneOn.isBigO_log_of_eventually_le {u : ℝ → ℝ} {x₀ C : ℝ}
    (h₁ : MonotoneOn u (Set.Ici x₀))
    (h₂ : ∀ᶠ r in volume.cofinite ⊓ atTop, u r ≤ C * Real.log r) :
    u =O[atTop] Real.log := by
  obtain ⟨s, hs, t, ht, hst⟩ := Filter.mem_inf_iff.1 h₂
  obtain ⟨R₀, hR₀⟩ := Filter.mem_atTop_sets.1 ht
  set M := (volume sᶜ).toReal with hM
  have hM₀ : 0 ≤ M := ENNReal.toReal_nonneg
  -- Beyond the threshold, every interval of length `M + 1` contains a good radius.
  have hgood : ∀ r, R₀ ≤ r → ∃ r', r ≤ r' ∧ r' ≤ r + (M + 1) ∧ u r' ≤ C * Real.log r' := by
    intro r hr
    rcases (Set.Icc r (r + (M + 1)) ∩ s).eq_empty_or_nonempty with hempty | hne
    · exfalso
      have h₃ : Set.Icc r (r + (M + 1)) ⊆ sᶜ := fun x hx hxs ↦
        Set.eq_empty_iff_forall_notMem.1 hempty x ⟨hx, hxs⟩
      have h₄ := measure_mono (μ := volume) h₃
      rw [Real.volume_Icc, show r + (M + 1) - r = M + 1 by ring] at h₄
      have h₅ : volume sᶜ ≤ ENNReal.ofReal M :=
        le_of_eq (ENNReal.ofReal_toReal (Measure.mem_cofinite.1 hs).ne).symm
      have h₆ := h₄.trans h₅
      rw [ENNReal.ofReal_le_ofReal_iff hM₀] at h₆
      linarith
    · obtain ⟨r', hr'⟩ := hne
      have h₇ : r' ∈ t := hR₀ r' (le_trans hr hr'.1.1)
      have h₈ : u r' ≤ C * Real.log r' := by
        have h₉ : r' ∈ s ∩ t := ⟨hr'.2, h₇⟩
        rw [← hst] at h₉
        exact h₉
      exact ⟨r', hr'.1.1, hr'.1.2, h₈⟩
  -- Assemble the `O(log)` bound.
  rw [isBigO_iff]
  refine ⟨max C 0 * (Real.log (M + 2) + 1) + |u (max x₀ R₀)|, ?_⟩
  filter_upwards [eventually_ge_atTop (max x₀ R₀), eventually_ge_atTop 1,
    eventually_ge_atTop (Real.exp 1)] with r hr₁ hr₂ hre
  have hlogr : 1 ≤ Real.log r := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hre
  obtain ⟨r', hrr', hr'M, hr'good⟩ := hgood r (le_trans (le_max_right x₀ R₀) hr₁)
  have hx₀r : x₀ ≤ r := le_trans (le_max_left x₀ R₀) hr₁
  -- Monotonicity transfers the bound from the good radius `r'` back to `r` …
  have h₃ : u r ≤ u r' := h₁ (Set.mem_Ici.2 hx₀r) (Set.mem_Ici.2 (le_trans hx₀r hrr')) hrr'
  have h₄ : Real.log r' ≤ Real.log (M + 2) + Real.log r := by
    have h₅ : r' ≤ (M + 2) * r := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ M + 1) (by linarith : (0 : ℝ) ≤ r - 1)]
    calc Real.log r'
        ≤ Real.log ((M + 2) * r) :=
          Real.log_le_log (lt_of_lt_of_le one_pos (le_trans hr₂ hrr')) h₅
      _ = Real.log (M + 2) + Real.log r := Real.log_mul (by linarith) (by linarith)
  have h₆ : 0 ≤ Real.log (M + 2) := Real.log_nonneg (by linarith)
  have h₇ : u r ≤ max C 0 * (Real.log (M + 2) + 1) * Real.log r := by
    calc u r
        ≤ C * Real.log r' := le_trans h₃ hr'good
      _ ≤ max C 0 * Real.log r' :=
          mul_le_mul_of_nonneg_right (le_max_left C 0)
            (Real.log_nonneg (le_trans hr₂ hrr'))
      _ ≤ max C 0 * (Real.log (M + 2) + Real.log r) :=
          mul_le_mul_of_nonneg_left h₄ (le_max_right C 0)
      _ ≤ max C 0 * ((Real.log (M + 2) + 1) * Real.log r) := by
          have h₈ : Real.log (M + 2) + Real.log r ≤ (Real.log (M + 2) + 1) * Real.log r := by
            nlinarith
          exact mul_le_mul_of_nonneg_left h₈ (le_max_right C 0)
      _ = max C 0 * (Real.log (M + 2) + 1) * Real.log r := by ring
  -- … while monotonicity from the base point bounds `u r` from below.
  have h₉ : u (max x₀ R₀) ≤ u r :=
    h₁ (Set.mem_Ici.2 (le_max_left x₀ R₀)) (Set.mem_Ici.2 hx₀r) hr₁
  have h₁₀ : 0 ≤ max C 0 * (Real.log (M + 2) + 1) :=
    mul_nonneg (le_max_right C 0) (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log r), abs_le]
  constructor
  · nlinarith [neg_abs_le (u (max x₀ R₀)), abs_nonneg (u (max x₀ R₀))]
  · nlinarith [abs_nonneg (u (max x₀ R₀))]

/-!
## Auxiliary Lemmas
-/

/-- The positive part of the logarithm grows sublinearly. -/
private lemma tendsto_posLog_div_atTop : Tendsto (fun x : ℝ ↦ log⁺ x / x) atTop (𝓝 0) := by
  apply Tendsto.congr' _ Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.posLog_eq_log (by rwa [abs_of_nonneg (by linarith)]), id_eq]

namespace ValueDistribution

/-!
## The Omission Predicate
-/

/--
The function `f` **omits** the value `a ∈ ℂ ∪ {∞}`.  The predicate is phrased through
meromorphic orders and therefore robust under junk values: `f` omits `⊤` if it has no
poles, and `f` omits a finite value `a₀` if `f - a₀` has no zeros — where a point with
`meromorphicOrderAt (f · - a₀) x = ⊤`, i.e. a point near which `f` is constantly equal to
`a₀`, also counts as an `a₀`-point.
-/
def Omits (f : ℂ → ℂ) : WithTop ℂ → Prop
  | ⊤ => ∀ x, 0 ≤ meromorphicOrderAt f x
  | (a₀ : ℂ) => ∀ x, meromorphicOrderAt (f · - a₀) x ≤ 0

variable {f g : ℂ → ℂ} {a₀ : ℂ}

/-- Definition unfolding: `f` omits `⊤` iff it has no poles. -/
@[simp] lemma omits_top_iff :
    Omits f ⊤ ↔ ∀ x, 0 ≤ meromorphicOrderAt f x := Iff.rfl

/-- Definition unfolding: `f` omits a finite value `a₀` iff `f - a₀` has no zeros. -/
@[simp] lemma omits_coe_iff :
    Omits f a₀ ↔ ∀ x, meromorphicOrderAt (f · - a₀) x ≤ 0 := Iff.rfl

/-- An analytic function that never attains a finite value `a₀` omits it. -/
lemma Omits.of_forall_ne (hf : ∀ x, AnalyticAt ℂ f x) (h : ∀ z, f z ≠ a₀) :
    Omits f a₀ := by
  rw [omits_coe_iff]
  intro x
  have h₁ : AnalyticAt ℂ (f · - a₀) x := (hf x).sub analyticAt_const
  have h₂ : meromorphicOrderAt (f · - a₀) x = 0 := by
    rw [h₁.meromorphicOrderAt_eq, h₁.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 (h x))]
    rfl
  exact h₂.le

/-- Omission transfers along equality away from a codiscrete set. -/
lemma Omits.congr {a : WithTop ℂ} (h : Omits f a) (hfg : f =ᶠ[codiscrete ℂ] g) :
    Omits g a := by
  have key : ∀ x, f =ᶠ[𝓝[≠] x] g := fun x ↦
    mem_codiscrete_iff_forall_mem_nhdsNE.1 (hfg : {z | f z = g z} ∈ codiscrete ℂ) x
  by_cases ha : a = ⊤
  · subst ha
    rw [omits_top_iff] at h ⊢
    intro x
    rw [← meromorphicOrderAt_congr (key x)]
    exact h x
  · lift a to ℂ using ha with b₀
    rw [omits_coe_iff] at h ⊢
    intro x
    have h₁ : (f · - b₀) =ᶠ[𝓝[≠] x] (g · - b₀) := by
      filter_upwards [key x] with z hz
      simp [hz]
    rw [← meromorphicOrderAt_congr h₁]
    exact h x

/-- The truncated counting function of an omitted value vanishes. -/
lemma Omits.truncatedLogCounting_eq_zero {a : WithTop ℂ} (hf : Meromorphic f)
    (h : Omits f a) : truncatedLogCounting f a = 0 := by
  by_cases ha : a = ⊤
  · subst ha
    have h₁ : (MeromorphicOn.divisor f Set.univ)⁻ = 0 := by
      apply negPart_eq_zero.2
      rw [Function.locallyFinsuppWithin.le_def]
      intro z
      rw [MeromorphicOn.divisor_apply (meromorphicOn_univ.2 hf) (Set.mem_univ z)]
      simpa using WithTop.untop₀_nonneg.mpr ((omits_top_iff.1 h) z)
    have h₂ : (MeromorphicOn.divisor f Set.univ)⁻.trunc = 0 := by
      rw [h₁]
      ext z
      simp
    rw [truncatedLogCounting_top, h₂, map_zero]
  · lift a to ℂ using ha with b₀
    have hfa : Meromorphic (f · - b₀) := by fun_prop
    have h₁ : (MeromorphicOn.divisor (f · - b₀) Set.univ)⁺ = 0 := by
      apply posPart_eq_zero.2
      rw [Function.locallyFinsuppWithin.le_def]
      intro z
      rw [MeromorphicOn.divisor_apply (meromorphicOn_univ.2 hfa) (Set.mem_univ z)]
      simpa using WithTop.untop₀_le_untop₀ (by simp) ((omits_coe_iff.1 h) z)
    have h₂ : (MeromorphicOn.divisor (f · - b₀) Set.univ)⁺.trunc = 0 := by
      rw [h₁]
      ext z
      simp
    rw [truncatedLogCounting_coe, h₂, map_zero]

/-!
## The Algebraic Core: Rational Functions Omitting Finite Values
-/

/--
If the rational function `p/q` omits the finite value `a`, and `p`, `q` have no common
root, then `p - a·q` is constant: any root `z₀` of `p - a·q` would either be a common
root of `p` and `q`, or a point where `p/q - a` vanishes continuously, forcing the
meromorphic order of `p/q - a` at `z₀` to be positive.  By the fundamental theorem of
algebra, a root-free polynomial is constant.
-/
private lemma exists_sub_C_mul_eq_C_of_omits {p q : Polynomial ℂ}
    (hpq : ∀ z, q.eval z = 0 → p.eval z ≠ 0) {a : ℂ} (h : Omits (p.eval / q.eval) a) :
    ∃ c, p - Polynomial.C a * q = Polynomial.C c := by
  by_cases hF : p - Polynomial.C a * q = 0
  · exact ⟨0, by rw [hF, map_zero]⟩
  -- The polynomial `p - a·q` has no roots.
  have hroot : ∀ z, (p - Polynomial.C a * q).eval z ≠ 0 := by
    intro z₀ hz₀
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, sub_eq_zero] at hz₀
    by_cases hqz : q.eval z₀ = 0
    · exact hpq z₀ hqz (by rw [hz₀, hqz, mul_zero])
    · -- `p/q − a` is continuous at `z₀` with value `0`, so its order there is positive.
      have h₁ : ContinuousAt (fun z ↦ p.eval z / q.eval z - a) z₀ :=
        (((Polynomial.differentiable p).continuous.continuousAt).div
          ((Polynomial.differentiable q).continuous.continuousAt) hqz).sub continuousAt_const
      have h₂ : p.eval z₀ / q.eval z₀ - a = 0 := by
        rw [hz₀, mul_div_assoc, div_self hqz, mul_one, sub_self]
      have h₃ : Tendsto (fun z ↦ p.eval z / q.eval z - a) (𝓝[≠] z₀) (𝓝 0) := by
        rw [← h₂]
        exact h₁.tendsto.mono_left nhdsWithin_le_nhds
      have h₄ : MeromorphicAt (fun z ↦ p.eval z / q.eval z - a) z₀ :=
        ((((Polynomial.differentiable p).analyticAt z₀).meromorphicAt).div
          (((Polynomial.differentiable q).analyticAt z₀).meromorphicAt)).sub (.const a z₀)
      have h₅ : (0 : WithTop ℤ) < meromorphicOrderAt ((p.eval / q.eval) · - a) z₀ :=
        (tendsto_zero_iff_meromorphicOrderAt_pos h₄).1 h₃
      exact absurd ((omits_coe_iff.1 h) z₀) (not_le.2 h₅)
  -- A root-free polynomial is constant (fundamental theorem of algebra).
  have hdeg : (p - Polynomial.C a * q).degree ≤ 0 := by
    by_contra hcon
    obtain ⟨z, hz⟩ := Complex.exists_root (not_le.1 hcon)
    exact hroot z hz
  exact ⟨(p - Polynomial.C a * q).coeff 0, Polynomial.eq_C_of_degree_le_zero hdeg⟩

/-!
## Picard's Little Theorem, Meromorphic Version
-/

/--
**Picard's little theorem**, meromorphic version: a meromorphic function on `ℂ` omitting
three values of `ℂ ∪ {∞}` is constant away from a discrete set.
-/
theorem eventuallyConst_of_omits {f : ℂ → ℂ} (hf : Meromorphic f)
    {S : Finset (WithTop ℂ)} (hcard : 3 ≤ S.card) (h : ∀ a ∈ S, Omits f a) :
    EventuallyConst f (codiscrete ℂ) := by
  classical
  -- Step 1: all truncated counting functions vanish, so the Second Main Theorem forces
  -- `T(r) ≤ c (log⁺ T(r) + log r)`; absorbing `log⁺ T` gives `T(r) ≤ C log r`, for all
  -- large `r` outside a set of finite measure.
  obtain ⟨c, hc⟩ := secondMainTheorem hf S
  set c' := max c 0 with hc'def
  have hc'0 : (0 : ℝ) ≤ c' := le_max_right c 0
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1
    (tendsto_posLog_div_atTop.eventually_le_const
      (show (0 : ℝ) < 1 / (2 * (c' + 1)) by positivity))
  have hbound : ∀ᶠ r in volume.cofinite ⊓ atTop,
      characteristic f ⊤ r ≤ (2 * c' + max x₁ 1) * Real.log r := by
    filter_upwards [hc, mem_inf_of_right (eventually_ge_atTop (Real.exp 1))] with r h₁ hre
    have hr1 : (1 : ℝ) ≤ r := by linarith [Real.add_one_le_exp 1]
    have hlogr : 1 ≤ Real.log r := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hre
    have hT0 : 0 ≤ characteristic f ⊤ r := characteristic_nonneg hr1
    have hpos : 0 ≤ log⁺ (characteristic f ⊤ r) + Real.log r := by
      linarith [posLog_nonneg (x := characteristic f ⊤ r)]
    -- All truncated counting terms vanish.
    have h₂ : ∑ a ∈ S, truncatedLogCounting f a r = 0 :=
      Finset.sum_eq_zero fun a ha ↦ by simp [(h a ha).truncatedLogCounting_eq_zero hf]
    -- From S2 and `#S ≥ 3`:
    have h₃ : characteristic f ⊤ r
        ≤ c' * log⁺ (characteristic f ⊤ r) + c' * Real.log r := by
      have h₄ : (1 : ℝ) ≤ (S.card : ℝ) - 2 := by
        have h₅ : (3 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard
        linarith
      have h₅ : c * (log⁺ (characteristic f ⊤ r) + Real.log r)
          ≤ c' * (log⁺ (characteristic f ⊤ r) + Real.log r) :=
        mul_le_mul_of_nonneg_right (le_max_left c 0) hpos
      have h₆ : characteristic f ⊤ r ≤ ((S.card : ℝ) - 2) * characteristic f ⊤ r :=
        le_mul_of_one_le_left hT0 h₄
      rw [h₂] at h₁
      nlinarith [h₁, h₅, h₆]
    -- Absorption: case split on the size of `T r`.
    by_cases hcase : max x₁ 1 ≤ characteristic f ⊤ r
    · have h₇ := hx₁ (characteristic f ⊤ r) (le_trans (le_max_left x₁ 1) hcase)
      have hTpos : 0 < characteristic f ⊤ r :=
        lt_of_lt_of_le one_pos (le_trans (le_max_right x₁ 1) hcase)
      rw [div_le_iff₀ hTpos] at h₇
      have h₈ : c' * log⁺ (characteristic f ⊤ r) ≤ characteristic f ⊤ r / 2 := by
        have h₉ : c' * (1 / (2 * (c' + 1))) ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) two_pos]
          linarith
        calc c' * log⁺ (characteristic f ⊤ r)
            ≤ c' * (1 / (2 * (c' + 1)) * characteristic f ⊤ r) :=
              mul_le_mul_of_nonneg_left h₇ hc'0
          _ = c' * (1 / (2 * (c' + 1))) * characteristic f ⊤ r := by ring
          _ ≤ 1 / 2 * characteristic f ⊤ r := mul_le_mul_of_nonneg_right h₉ hT0
          _ = characteristic f ⊤ r / 2 := by ring
      have h₉ : 0 ≤ max x₁ 1 * Real.log r :=
        mul_nonneg (le_trans zero_le_one (le_max_right x₁ 1)) (by linarith)
      linarith
    · push Not at hcase
      have h₇ : max x₁ 1 ≤ max x₁ 1 * Real.log r :=
        le_mul_of_one_le_right (le_trans zero_le_one (le_max_right x₁ 1)) hlogr
      have h₈ : 0 ≤ 2 * c' * Real.log r := by positivity
      linarith
  -- Step 2: remove the exceptional set — the characteristic is `O(log)` outright, so `f`
  -- is rational.
  have hOlog : characteristic f ⊤ =O[atTop] Real.log :=
    MonotoneOn.isBigO_log_of_eventually_le
      ((characteristic_monotoneOn hf).mono fun x hx ↦ mem_Ioi.2 (lt_of_lt_of_le one_pos hx))
      hbound
  obtain ⟨p, q, hq0, hfpq⟩ :=
    (rational_iff_characteristic_isBigO_log (meromorphicOn_univ.2 hf)).2 hOlog
  -- Step 3: pass to coprime representatives `p'`, `q'`.
  obtain ⟨p', q', g, hrel, hgp, hgq⟩ := UniqueFactorizationMonoid.exists_reduced_factors' p q hq0
  have hg0 : g ≠ 0 := by
    apply left_ne_zero_of_mul (b := q')
    rw [hgq]
    exact hq0
  have hfpq' : f =ᶠ[codiscrete ℂ] p'.eval / q'.eval := by
    apply hfpq.trans
    filter_upwards [Polynomial.eventually_eval_ne_zero_codiscrete hg0] with z hgz
    rw [Pi.div_apply, Pi.div_apply, ← hgp, ← hgq, Polynomial.eval_mul, Polynomial.eval_mul]
    exact mul_div_mul_left _ _ hgz
  have hno : ∀ z, q'.eval z = 0 → p'.eval z ≠ 0 := fun z hqz hpz ↦
    Polynomial.not_isUnit_X_sub_C z
      (hrel (Polynomial.dvd_iff_isRoot.2 hpz) (Polynomial.dvd_iff_isRoot.2 hqz))
  -- Step 4: `S` contains two distinct finite values; the algebraic core forces the
  -- rational model to be constant.
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ S.erase ⊤, ∃ b ∈ S.erase ⊤, a ≠ b := by
    apply Finset.one_lt_card.1
    have h₁ := Finset.pred_card_le_card_erase (s := S) (a := ⊤)
    omega
  obtain ⟨hane, haS⟩ := Finset.mem_erase.1 ha
  obtain ⟨hbne, hbS⟩ := Finset.mem_erase.1 hb
  lift a to ℂ using hane with a₀
  lift b to ℂ using hbne with b₀
  have hab' : a₀ ≠ b₀ := fun hcon ↦ hab (by rw [hcon])
  obtain ⟨c₁, hc₁⟩ := exists_sub_C_mul_eq_C_of_omits hno ((h ↑a₀ haS).congr hfpq')
  obtain ⟨c₂, hc₂⟩ := exists_sub_C_mul_eq_C_of_omits hno ((h ↑b₀ hbS).congr hfpq')
  -- Subtract: `q'` and `p'` are constant polynomials.
  set k := (c₁ - c₂) / (b₀ - a₀) with hk
  have hne : b₀ - a₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hab')
  have hq'const : q' = Polynomial.C k := by
    have h₁ : Polynomial.C (b₀ - a₀) * q' = Polynomial.C (c₁ - c₂) := by
      rw [Polynomial.C_sub, Polynomial.C_sub, ← hc₁, ← hc₂]
      ring
    have h₂ : Polynomial.C (b₀ - a₀) ≠ (0 : Polynomial ℂ) := Polynomial.C_ne_zero.2 hne
    apply mul_left_cancel₀ h₂
    rw [h₁, ← Polynomial.C_mul, hk]
    congr 1
    field_simp
  have hp'const : p' = Polynomial.C (c₁ + a₀ * k) := by
    have h₁ : p' = Polynomial.C c₁ + Polynomial.C a₀ * q' := by
      rw [← hc₁]
      ring
    rw [h₁, hq'const, ← Polynomial.C_mul, ← Polynomial.C_add]
  -- Conclude: `f` agrees with the constant `(c₁ + a₀ k)/k` away from a discrete set.
  rw [eventuallyConst_iff_exists_eventuallyEq]
  refine ⟨(c₁ + a₀ * k) / k, ?_⟩
  filter_upwards [hfpq'] with z hz
  rw [hz, Pi.div_apply, hp'const, hq'const, Polynomial.eval_C, Polynomial.eval_C]

end ValueDistribution

/-!
## Picard's Little Theorem, Entire Version
-/

/--
**Picard's little theorem**: an entire function that omits two distinct finite values is
constant.
-/
theorem Differentiable.exists_eq_const_of_forall_ne {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a b : ℂ} (hab : a ≠ b) (ha : ∀ z, f z ≠ a) (hb : ∀ z, f z ≠ b) :
    ∃ c, f = fun _ ↦ c := by
  have hana : ∀ x, AnalyticAt ℂ f x := fun x ↦ hf.analyticAt x
  have hmero : Meromorphic f := fun x ↦ (hana x).meromorphicAt
  -- `f` omits the three values `a`, `b`, `∞`.
  have hcard : 3 ≤ ({↑a, ↑b, ⊤} : Finset (WithTop ℂ)).card := by
    rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_insert_of_notMem (by simp),
      Finset.card_singleton]
  have homits : ∀ v ∈ ({↑a, ↑b, ⊤} : Finset (WithTop ℂ)), ValueDistribution.Omits f v := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact ValueDistribution.Omits.of_forall_ne hana ha
    · exact ValueDistribution.Omits.of_forall_ne hana hb
    · exact fun x ↦ (hana x).meromorphicOrderAt_nonneg
  -- Picard's little theorem, meromorphic version:
  have hconst := ValueDistribution.eventuallyConst_of_omits hmero hcard homits
  rw [eventuallyConst_iff_exists_eventuallyEq] at hconst
  obtain ⟨c, hc⟩ := hconst
  -- Upgrade eventual constancy to constancy, by the identity theorem.
  refine ⟨c, ?_⟩
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = c := mem_codiscrete_iff_forall_mem_nhdsNE.1 hc 0
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = c := hev.frequently
  have h₁ := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (fun z _ ↦ hana z)
    analyticOnNhd_const isPreconnected_univ (Set.mem_univ 0) hfreq
  funext z
  exact h₁ (Set.mem_univ z)
