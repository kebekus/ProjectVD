/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import VD.MathlibSubmitted.LogCountingIsBigOLog
import VD.MathlibPending.BoundednessCharacteristic

/-!
# Rational Functions and the Growth of the Characteristic Function

We characterize the rational functions in terms of the growth of their characteristic function: a
function `f : ℂ → ℂ` that is meromorphic on `ℂ` agrees, away from a codiscrete set, with a rational
function if and only if its characteristic function is big-O of `log`.  Specializing to functions
without poles, an entire function `f : ℂ → ℂ` is a polynomial if and only if its characteristic
function is big-O of `log`.

This is the analogue, at the scale of `log`, of the boundedness characterization of constant
functions established in `VD.MathlibPending.BoundednessCharacteristic`, and formalizes the
characterization of rational functions discussed in Theorem 2.6 on p. 170 of [Lang, *Introduction to
Complex Hyperbolic Spaces*][MR886677].
-/

open Asymptotics Filter Function MeromorphicOn Real Set Topology

namespace ValueDistribution

/-!
## Auxiliary facts about polynomials
-/

/-- A polynomial defines an entire function. -/
private lemma analyticOnNhd_polynomial (p : Polynomial ℂ) :
    AnalyticOnNhd ℂ (fun z ↦ p.eval z) univ :=
  fun z _ ↦ (Polynomial.differentiable p).analyticAt z

/-- A nonzero polynomial is nowhere locally constant zero. -/
private lemma polynomial_meromorphicOrderAt_ne_top {p : Polynomial ℂ} (hp : p ≠ 0) (z : ℂ) :
    meromorphicOrderAt (fun w ↦ p.eval w) z ≠ ⊤ := by
  have hana : AnalyticAt ℂ (fun w ↦ p.eval w) z := (Polynomial.differentiable p).analyticAt z
  rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero hana.meromorphicAt]
  by_contra h
  rw [Filter.not_eventually] at h
  simp only [not_not] at h
  rw [hana.frequently_zero_iff_eventually_zero] at h
  exact hp (Polynomial.eq_zero_of_infinite_isRoot p (infinite_of_mem_nhds z h))

/-- The characteristic function of the zero function vanishes. -/
private lemma characteristic_zero_top : characteristic (0 : ℂ → ℂ) ⊤ = 0 := by
  unfold characteristic
  simp only [logCounting_const_zero, add_zero]
  funext r
  rw [proximity_top]
  simp [circleAverage_const]

/-- The characteristic function of a polynomial is `O(log)`. -/
private lemma characteristic_polynomial_isBigO_log (p : Polynomial ℂ) :
    characteristic (fun z ↦ p.eval z) ⊤ =O[atTop] Real.log := by
  have hlc : logCounting (fun z ↦ p.eval z) ⊤ = 0 := by
    rw [logCounting_top, show (divisor (fun z ↦ p.eval z) univ)⁻ = 0 from
      negPart_eq_zero.2 (analyticOnNhd_polynomial p).divisor_nonneg, map_zero]
  rw [show characteristic (fun z ↦ p.eval z) ⊤ = proximity (fun z ↦ p.eval z) ⊤ from by
    unfold characteristic; rw [hlc, add_zero]]
  exact proximity_isBigO_log_of_polynomial p

/--
A function `f : ℂ → ℂ` that is meromorphic on `ℂ` agrees, away from a codiscrete set, with a
rational function if and only if its characteristic function is big-O of `log`.
-/
theorem rational_iff_characteristic_isBigO_log {f : ℂ → ℂ} (hf : MeromorphicOn f Set.univ) :
    (∃ p q : Polynomial ℂ, q ≠ 0 ∧ f =ᶠ[codiscrete ℂ] p.eval / q.eval) ↔
      characteristic f ⊤ =O[atTop] Real.log := by
  constructor
  · rintro ⟨p, q, hq, hfg⟩
    have hcong : characteristic f ⊤ =ᶠ[atTop] characteristic (p.eval / q.eval) ⊤ := by
      filter_upwards [eventually_ne_atTop 0] with r hr using characteristic_congr_codiscrete hfg hr
    rw [Asymptotics.isBigO_congr hcong EventuallyEq.rfl]
    by_cases hp : p = 0
    · subst hp
      rw [show ((0 : Polynomial ℂ).eval / q.eval) = (0 : ℂ → ℂ) from by funext z; simp,
        characteristic_zero_top]
      exact Asymptotics.isBigO_zero _ _
    rw [show (p.eval / q.eval) = (fun z ↦ p.eval z) * (fun z ↦ q.eval z)⁻¹ from by
      funext z; simp [div_eq_mul_inv]]
    have hpm : Meromorphic fun z ↦ p.eval z :=
      fun z ↦ (analyticOnNhd_polynomial p z (mem_univ z)).meromorphicAt
    have hqm : Meromorphic fun z ↦ q.eval z :=
      fun z ↦ (analyticOnNhd_polynomial q z (mem_univ z)).meromorphicAt
    have hqinvm : Meromorphic (fun z ↦ q.eval z)⁻¹ := fun z ↦ (hqm z).inv
    have hqinvord : ∀ z, meromorphicOrderAt (fun w ↦ q.eval w)⁻¹ z ≠ ⊤ := by
      intro z
      rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hqinvm z)]
      filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hqm z)).1
        (polynomial_meromorphicOrderAt_ne_top hq z)] with w hw
      simpa using inv_ne_zero hw
    have hmulle := characteristic_mul_top_eventuallyLE hpm
      (polynomial_meromorphicOrderAt_ne_top hp) hqinvm hqinvord
    have h1 : characteristic (fun z ↦ p.eval z) ⊤ =O[atTop] Real.log :=
      characteristic_polynomial_isBigO_log p
    have h2 : characteristic (fun z ↦ q.eval z)⁻¹ ⊤ =O[atTop] Real.log := by
      have hone : (1 : ℝ → ℝ) =O[atTop] Real.log := isLittleO_const_log_atTop.isBigO
      have hD : (characteristic (fun z ↦ q.eval z) ⊤ - characteristic (fun z ↦ q.eval z)⁻¹ ⊤)
          =O[atTop] Real.log := (isBigO_characteristic_sub_characteristic_inv hqm).trans hone
      rw [show characteristic (fun z ↦ q.eval z)⁻¹ ⊤ = characteristic (fun z ↦ q.eval z) ⊤
        - (characteristic (fun z ↦ q.eval z) ⊤ - characteristic (fun z ↦ q.eval z)⁻¹ ⊤) from
        (sub_sub_cancel _ _).symm]
      exact (characteristic_polynomial_isBigO_log q).sub hD
    have hsum := h1.add h2
    refine Asymptotics.IsBigO.trans ?_ hsum
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [hmulle,
      characteristic_eventually_nonneg (f := (fun z ↦ p.eval z) * (fun z ↦ q.eval z)⁻¹) (a := ⊤),
      characteristic_eventually_nonneg (f := fun z ↦ p.eval z) (a := ⊤),
      characteristic_eventually_nonneg (f := (fun z ↦ q.eval z)⁻¹) (a := ⊤)] with r hle hg hpa hqa
    rw [one_mul, Real.norm_of_nonneg hg, Real.norm_of_nonneg (add_nonneg hpa hqa)]
    exact hle
  · intro hO
    obtain ⟨_, hlog⟩ := characteristic_isBigO_iff.1 hO
    have hfmero : Meromorphic f := fun z ↦ hf z (mem_univ z)
    by_cases hH : ∀ z, meromorphicOrderAt f z ≠ ⊤
    · -- Pole-clearing: multiply `f` by a polynomial `q` whose zeros are the poles of `f`.
      classical
      have hDfin : ((divisor f univ)⁻).support.Finite :=
        (logCounting_isBigO_log_iff_finite_support (f := f)).1 hlog
      have hd : Function.HasFiniteSupport fun u ↦ (divisor f univ)⁻ u := hDfin
      have hnn : ∀ u, 0 ≤ (divisor f univ)⁻ u := fun u ↦ by
        simpa using Function.locallyFinsuppWithin.le_def.1 (negPart_nonneg (divisor f univ)) u
      set q : Polynomial ℂ :=
        ∏ u ∈ hDfin.toFinset, (Polynomial.X - Polynomial.C u) ^ ((divisor f univ)⁻ u).toNat
        with hq_def
      have hq0 : q ≠ 0 := by
        rw [hq_def]
        exact Finset.prod_ne_zero_iff.2 fun u _ ↦ pow_ne_zero _ (Polynomial.X_sub_C_ne_zero u)
      have hqeval : (fun z ↦ q.eval z) = ∏ᶠ u, (· - u) ^ ((divisor f univ)⁻ u) := by
        funext z
        have hsub : (Function.mulSupport fun u ↦ (z - u) ^ ((divisor f univ)⁻ u)) ⊆
            hDfin.toFinset := by
          intro u hu
          by_contra hu2
          simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support, ne_eq,
            not_not] at hu2
          exact hu (by change (z - u) ^ ((divisor f univ)⁻ u) = 1; rw [hu2, zpow_zero])
        rw [show (∏ᶠ u, (· - u) ^ ((divisor f univ)⁻ u)) z
            = ∏ u ∈ hDfin.toFinset, (z - u) ^ ((divisor f univ)⁻ u) from by
          rw [Function.FactorizedRational.finprod_eq_fun hd]
          exact finprod_eq_prod_of_mulSupport_subset _ hsub]
        rw [hq_def, Polynomial.eval_prod]
        refine Finset.prod_congr rfl fun u _ ↦ ?_
        rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
          ← zpow_natCast, Int.toNat_of_nonneg (hnn u)]
      have hqdiv : divisor (fun z ↦ q.eval z) univ = (divisor f univ)⁻ := by
        rw [hqeval]; exact Function.FactorizedRational.divisor hDfin
      have hqmero : Meromorphic fun z ↦ q.eval z :=
        fun z ↦ (analyticOnNhd_polynomial q z (mem_univ z)).meromorphicAt
      have hqmeroOn : MeromorphicOn (fun z ↦ q.eval z) univ := fun z _ ↦ hqmero z
      have hQord : ∀ z, meromorphicOrderAt (fun w ↦ q.eval w) z ≠ ⊤ :=
        polynomial_meromorphicOrderAt_ne_top hq0
      set g : ℂ → ℂ := f * fun z ↦ q.eval z with hg_def
      have hgmero : MeromorphicOn g univ := hf.mul hqmeroOn
      have hgdiv : divisor g univ = (divisor f univ)⁺ := by
        rw [hg_def, divisor_mul hf hqmeroOn (fun z _ ↦ hH z) (fun z _ ↦ hQord z), hqdiv]
        exact (eq_add_of_sub_eq (posPart_sub_negPart (divisor f univ))).symm
      have hg0ana : AnalyticOnNhd ℂ (toMeromorphicNFOn g univ) univ := by
        rw [← (meromorphicNFOn_toMeromorphicNFOn g univ).divisor_nonneg_iff_analyticOnNhd,
          MeromorphicOn.divisor_of_toMeromorphicNFOn hgmero, hgdiv]
        exact posPart_nonneg _
      -- `characteristic g ⊤` is `O(log)`, hence so is `proximity` of the (entire) normal form.
      have hcharg : characteristic g ⊤ =O[atTop] Real.log := by
        have hsum := hO.add (characteristic_polynomial_isBigO_log q)
        have hle : characteristic g ⊤ ≤ᶠ[atTop]
            characteristic f ⊤ + characteristic (fun z ↦ q.eval z) ⊤ := by
          rw [hg_def]; exact characteristic_mul_top_eventuallyLE hfmero (fun z ↦ hH z) hqmero hQord
        refine Asymptotics.IsBigO.trans ?_ hsum
        rw [Asymptotics.isBigO_iff]
        refine ⟨1, ?_⟩
        filter_upwards [hle, characteristic_eventually_nonneg (f := g) (a := ⊤),
          characteristic_eventually_nonneg (f := f) (a := ⊤),
          characteristic_eventually_nonneg (f := fun z ↦ q.eval z) (a := ⊤)] with r hr h1 h2 h3
        rw [one_mul, Real.norm_of_nonneg h1, Real.norm_of_nonneg (add_nonneg h2 h3)]
        exact hr
      have hpx0 : proximity (toMeromorphicNFOn g univ) ⊤ =O[atTop] Real.log := by
        have hpg : proximity g ⊤ =O[atTop] Real.log := (characteristic_isBigO_iff.1 hcharg).1
        have heq := proximity_eq_proximity_toMeromorphicNFOn (a := (⊤ : WithTop ℂ)) hgmero
        rw [Set.top_eq_univ] at heq
        exact (Asymptotics.isBigO_congr heq EventuallyEq.rfl).1 hpg
      obtain ⟨pp, hpp⟩ := (proximity_isBigO_log_iff_exists_eq_polynomial hg0ana).1 hpx0
      have hg_eq : g =ᶠ[codiscrete ℂ] fun z ↦ pp.eval z := by
        have := toMeromorphicNFOn_eqOn_codiscrete hgmero
        rw [hpp] at this
        exact this
      -- `q` is nonzero on a codiscrete set, so we can divide.
      have hqne0 : ∀ᶠ z in codiscrete ℂ, q.eval z ≠ 0 := by
        obtain ⟨x₀, hx₀⟩ : ∃ x, q.eval x ≠ 0 := by
          by_contra h
          simp only [not_exists, not_ne_iff] at h
          refine hq0 (Polynomial.eq_zero_of_infinite_isRoot q ?_)
          have : {x : ℂ | q.IsRoot x} = univ := by
            ext x; simp [Polynomial.IsRoot.def, h x]
          rw [this]; exact Set.infinite_univ
        filter_upwards [(analyticOnNhd_polynomial q).preimage_zero_mem_codiscreteWithin hx₀
          (mem_univ x₀) isConnected_univ] with z hz using hz
      refine ⟨pp, q, hq0, ?_⟩
      filter_upwards [hg_eq, hqne0] with z hgz hqz
      have hfq : f z * q.eval z = pp.eval z := by simpa [hg_def] using hgz
      rw [Pi.div_apply]
      exact (eq_div_iff hqz).2 hfq
    · -- `f` vanishes to infinite order somewhere, hence is `0` away from a codiscrete set.
      simp only [not_forall, not_ne_iff] at hH
      have hAll : ∀ z, meromorphicOrderAt f z = ⊤ := by
        intro z
        by_contra hz
        obtain ⟨z₀, hz₀⟩ := hH
        exact ((hf.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1
          ⟨⟨z, mem_univ z⟩, hz⟩ ⟨z₀, mem_univ z₀⟩) hz₀
      have hf0 : f =ᶠ[codiscrete ℂ] 0 := by
        have hmem : {z : ℂ | f z = 0} ∈ codiscrete ℂ := by
          rw [Filter.codiscrete, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
          intro x _
          rw [compl_univ, union_empty]
          exact meromorphicOrderAt_eq_top_iff.1 (hAll x)
        filter_upwards [hmem] with z hz using hz
      exact ⟨0, 1, one_ne_zero, by filter_upwards [hf0] with z hz; simp [hz]⟩

/--
An entire function `f : ℂ → ℂ` is a polynomial if and only if its characteristic function is
big-O of `log`.
-/
theorem polynomial_iff_characteristic_isBigO_log {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) :
    (∃ p : Polynomial ℂ, f = p.eval) ↔
      characteristic f ⊤ =O[atTop] Real.log := by
  have hlc : logCounting f ⊤ = 0 := by
    rw [logCounting_top, show (divisor f univ)⁻ = 0 from negPart_eq_zero.2 hf.divisor_nonneg,
      map_zero]
  have hchar : characteristic f ⊤ = proximity f ⊤ := by unfold characteristic; rw [hlc, add_zero]
  rw [hchar]
  exact (proximity_isBigO_log_iff_exists_eq_polynomial hf).symm

end ValueDistribution
