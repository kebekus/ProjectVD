/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic

/-!
## Polynomial Growth and Liouville-type Rigidity

General complex-analysis facts, independent of value distribution theory: a polynomial grows at
most polynomially, and conversely an entire function of polynomial growth is a polynomial.
-/

open Asymptotics Bornology Complex ComplexConjugate Filter Function MeromorphicOn Metric Real Set
open scoped Topology

variable {f : ℂ → ℂ} {U : Set ℂ} {x z w : ℂ} {R : ℝ}

/-- A polynomial function is `O(z ^ p.natDegree)` along `cobounded`. -/
theorem Polynomial.isBigO_cobounded_pow_natDegree {R : Type*} [NormedRing R] [NormMulClass R]
    (p : Polynomial R) :
    p.eval =O[cobounded R] (· ^ p.natDegree) :=
  isEquivalent_cobounded_leading_monomial.isBigO.trans (isBigO_const_mul_self _ _ _)

section DSlope

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f : 𝕜 → E} {s : Set 𝕜} {a z : 𝕜}

/--
Away from the base point `a`, the function `dslope f a` is analytic within `s` at `z` as soon as `f`
is.
-/
theorem AnalyticWithinAt.dslope_of_ne (hf : AnalyticWithinAt 𝕜 f s z) (hz : z ≠ a) :
    AnalyticWithinAt 𝕜 (dslope f a) s z := by
  have h : AnalyticWithinAt 𝕜 (fun w ↦ (w - a)⁻¹ • (f w - f a)) s z :=
    ((analyticWithinAt_id.sub analyticWithinAt_const).inv (sub_ne_zero.2 hz)).smul
      (hf.sub analyticWithinAt_const)
  refine h.congr_of_eventuallyEq_insert ?_
  filter_upwards [nhdsWithin_le_nhds (dslope_eventuallyEq_slope_of_ne f hz)] with w hw
  rw [hw, slope_def_module]

/--
If `f` is analytic at `z`, then so is the divided-difference function `dslope f a`, for any base
point `a`.
-/
@[fun_prop] protected theorem AnalyticAt.dslope (hf : AnalyticAt 𝕜 f z) (a : 𝕜) :
    AnalyticAt 𝕜 (dslope f a) z := by
  rcases eq_or_ne z a with rfl | hz
  · obtain ⟨p, hp⟩ := hf
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  · exact analyticWithinAt_univ.1 (hf.analyticWithinAt.dslope_of_ne hz)

/--
If `f` is analytic on `s` and the base point `a` does not lie in `s`, then `dslope f a` is analytic
on `s`.
-/
theorem AnalyticOn.dslope_of_notMem (hf : AnalyticOn 𝕜 f s) (ha : a ∉ s) :
    AnalyticOn 𝕜 (dslope f a) s :=
  fun z hz ↦ (hf z hz).dslope_of_ne (ne_of_mem_of_not_mem hz ha)

/--
If `f` is analytic on a set `s` that is a neighbourhood of the base point `a`, then `dslope f a` is
analytic on `s`.
-/
protected theorem AnalyticOn.dslope (hf : AnalyticOn 𝕜 f s) (ha : s ∈ 𝓝 a) :
    AnalyticOn 𝕜 (dslope f a) s := by
  intro z hz
  rcases eq_or_ne z a with hz' | hz'
  · have hfa : AnalyticAt 𝕜 f a :=
      analyticWithinAt_univ.1 ((hf a (mem_of_mem_nhds ha)).mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds ha))
    exact hz' ▸ (hfa.dslope a).analyticWithinAt
  · exact (hf z hz).dslope_of_ne hz'

/--
If `f` is analytic on a neighbourhood of `s`, then so is `dslope f a`, for any base point `a`.
-/
@[fun_prop] protected theorem AnalyticOnNhd.dslope (hf : AnalyticOnNhd 𝕜 f s) (a : 𝕜) :
    AnalyticOnNhd 𝕜 (dslope f a) s :=
  fun z hz ↦ (hf z hz).dslope a

end DSlope

/--
**Liouville's theorem for polynomial growth**: an entire function `f : ℂ → ℂ` that is
`O(z ^ n)` along `cobounded` is a polynomial of degree at most `n`.
-/
theorem Differentiable.exists_eq_polynomial_eval_of_isBigO_pow {n : ℕ} (hf : Differentiable ℂ f)
    (hg : f =O[cobounded ℂ] (· ^ n)) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ f = p.eval := by
  induction n generalizing f with
  | zero =>
    obtain ⟨C, hg⟩ := isBigO_iff.1 hg
    simp only [pow_zero, norm_one, mul_one] at hg
    have hK : IsBounded {z : ℂ | C < ‖f z‖} := by
      have : IsBounded {z : ℂ | ‖f z‖ ≤ C}ᶜ := isBounded_compl_iff.2 hg
      simpa only [compl_ofPred, not_le] using this
    have hbdd : IsBounded (range f) := by
      have himg : IsBounded (f '' {z : ℂ | C < ‖f z‖}) :=
        ((hK.isCompact_closure.image hf.continuous).isBounded).subset
          (image_mono subset_closure)
      refine (himg.union (isBounded_closedBall (x := (0 : ℂ)) (r := C))).subset ?_
      rintro _ ⟨z, rfl⟩
      by_cases hz : C < ‖f z‖
      · exact Or.inl ⟨z, hz, rfl⟩
      · exact Or.inr (by simp only [mem_closedBall, dist_zero_right]; exact not_lt.mp hz)
    obtain ⟨c, hc⟩ := hf.exists_eq_const_of_bounded hbdd
    exact ⟨Polynomial.C c, by simp, by rw [hc]; ext z; simp⟩
  | succ n ih =>
    obtain ⟨C, hg⟩ := isBigO_iff.1 hg
    simp only [norm_pow] at hg
    have e1 : ∀ᶠ z in cobounded ℂ, (1 : ℝ) ≤ ‖z‖ := eventually_cobounded_le_norm (E := ℂ) 1
    have hgrowth : dslope f 0 =O[cobounded ℂ] (· ^ n) := by
      refine IsBigO.of_bound (C + ‖f 0‖) ?_
      filter_upwards [hg, e1] with z hz h1z
      have hz0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at h1z; linarith
      rw [norm_pow, dslope_of_ne f hz0, slope_def_field, sub_zero, norm_div,
        div_le_iff₀ (by positivity), mul_assoc, ← pow_succ]
      have hpow : (1 : ℝ) ≤ ‖z‖ ^ (n + 1) := one_le_pow₀ h1z
      nlinarith [norm_sub_le (f z) (f 0), hz, norm_nonneg (f 0),
        mul_nonneg (norm_nonneg (f 0)) (sub_nonneg.2 hpow)]
    have hdf : Differentiable ℂ (dslope f 0) :=
      analyticOnNhd_univ_iff_differentiable.1
        ((analyticOnNhd_univ_iff_differentiable.2 hf).dslope 0)
    obtain ⟨q, hqn, hq⟩ := ih hdf hgrowth
    refine ⟨Polynomial.X * q + Polynomial.C (f 0), ?_, ?_⟩
    · calc (Polynomial.X * q + Polynomial.C (f 0)).natDegree
          = (Polynomial.X * q).natDegree := Polynomial.natDegree_add_C
        _ ≤ Polynomial.X.natDegree + q.natDegree := Polynomial.natDegree_mul_le
        _ ≤ 1 + n := add_le_add Polynomial.natDegree_X_le hqn
        _ = n + 1 := add_comm _ _
    · funext z
      have hid : z • dslope f 0 z = f z - f 0 := by
        have h := sub_smul_dslope f 0 z; rwa [sub_zero] at h
      simp only [hq, smul_eq_mul] at hid
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
      rw [hid]; ring
