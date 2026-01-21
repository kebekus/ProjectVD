import Mathlib.Analysis.Complex.ValueDistribution.CountingFunction

open Asymptotics Filter Function Real Set Classical

/-!
# Asymptotic Behaviour of Logarithmic Counting Functions


Prove that the logarithmic counting function of a meromorphic function `f` is
bounded if and only if `f` is analytic.
-/

namespace Function.locallyFinsuppWithin

variable
  {E : Type*} [NormedAddCommGroup E]

/-!
## Singleton Indicators as Functions with Locally Finite Support
-/

/--
Is analogy to `Finsupp.single`, this definition presents the indicator function
of a single point as a function with locally finite support.
-/
noncomputable def single (e : E) : locallyFinsuppWithin (Set.univ : Set E) ℤ where
  toFun := (if · = e then 1 else 0)
  supportWithinDomain' z hz := by tauto
  supportLocallyFiniteWithinDomain' := by
    intro _ _
    use ⊤
    simp [(by aesop : (if · = e then 1 else 0 : E → ℤ).support = {e})]

/--
Simplifier lemma: `single e` takes the value `1` at `e` and is zero otherwise.
-/
@[simp] lemma single_eval {e₁ e₂ : E} :
    single e₁ e₂ = if e₂ = e₁ then 1 else 0 := rfl

/--
The function `single e` is positive.
-/
@[simp] lemma single_pos {e : E} : 0 < single e := by
  apply lt_of_le_of_ne
  · intro x
    by_cases he : x = e
    all_goals
      simp_all [single_eval]
  · apply DFunLike.ne_iff.2
    use e
    simp [single_eval]

/--
Every positive function with locally finite supports dominates a singleton
indicator.
-/
lemma le_single [ProperSpace E] {D : locallyFinsuppWithin (univ : Set E) ℤ} (h : 0 < D) :
    ∃ e, single e ≤ D := by
  obtain ⟨z, hz⟩ := (by simpa [D.ext_iff] using (ne_of_lt h).symm : ∃ z, D z ≠ 0)
  use z
  intro e
  by_cases he : e = z
  · subst he
    simpa [single_eval] using Int.lt_iff_le_and_ne.mpr ⟨h.le e, hz.symm⟩
  · simpa [he, single_eval] using h.le e

/-!
## Logarithmic Counting Functions of Singleton Indicators
-/

/--
The logarithmic counting function of attached to the zero divisor is the zero
function.
-/
@[simp] lemma logCounting_zero [ProperSpace E]  :
    logCounting (0 : Function.locallyFinsuppWithin (Set.univ : Set E) ℤ) = 0 := by
  exact map_zero logCounting

/--
The logarithmic counting function of attached to a singleton indicator is
asymptotically equal to `log · - log ‖e‖`.
-/
@[simp] lemma logCounting_single_eq_log_sub_const [ProperSpace E] {e : E} {r : ℝ} (hr : ‖e‖ ≤ r) :
    logCounting (single e) r = log r - log ‖e‖ := by
  simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset _ (s := (finite_singleton e).toFinset)
    (by simp_all [toClosedBall, restrict_apply, single_eval])]
  simp only [toFinite_toFinset, toFinset_singleton, Finset.sum_singleton]
  rw [toClosedBall_eval_within _ (by simpa [abs_of_nonneg ((norm_nonneg e).trans hr)])]
  by_cases he : 0 = e
  · simp [← he, single_eval]
  · simp only [single_eval, he, reduceIte, Int.cast_zero, zero_mul, add_zero,
      log_mul (ne_of_lt (lt_of_lt_of_le (norm_pos_iff.mpr (he ·.symm)) hr)).symm
      (inv_ne_zero (norm_ne_zero_iff.mpr (he ·.symm))), log_inv]
    ring

/--
Qualitative consequence of `logCounting_single_eq_log_sub_const`. The constant
function `1 : ℝ → ℝ` is little o of the logarithmic counting function attached
to `single e`.
-/
lemma one_isLittleO_logCounting_single [ProperSpace E] {e : E} :
    (1 : ℝ → ℝ) =o[atTop] logCounting (single e) := by
  rw [isLittleO_iff]
  intro c hc
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, norm_eq_abs, eventually_atTop,
    ge_iff_le]
  use exp (|log ‖e‖| + c⁻¹)
  intro b hb
  have h₁b : 1 ≤ b := by
    calc 1
      _ ≤ exp (|log ‖e‖| + c⁻¹) :=
        one_le_exp (add_nonneg (abs_nonneg (log ‖e‖)) (inv_pos.2 hc).le)
      _ ≤ b := hb
  have h₁c : ‖e‖ ≤ exp (|log ‖e‖| + c⁻¹) := by
    calc ‖e‖
      _ ≤ exp (log ‖e‖) := by
        by_cases he : ‖e‖ = 0
        · simp [he]
        · simp_all [exp_log]
      _ ≤ exp (|log ‖e‖| + c⁻¹) :=
        exp_monotone (le_add_of_le_of_nonneg (le_abs_self _) (inv_pos.2 hc).le)
  rw [← inv_mul_le_iff₀ hc, mul_one, abs_of_nonneg (logCounting_nonneg single_pos.le h₁b)]
  calc c⁻¹
    _ ≤ logCounting (single e) (exp (|log ‖e‖| + c⁻¹)) := by
      simp [logCounting_single_eq_log_sub_const h₁c, le_sub_iff_add_le', le_abs_self (log ‖e‖)]
    _ ≤ logCounting (single e) b := by
      apply logCounting_mono single_pos.le (mem_Ioi.2 (exp_pos _)) _ hb
      simpa [mem_Ioi] using one_pos.trans_le h₁b

/-!
## Monotonicity of Logarithmic Counting Functions
-/

/--
The logarithmic counting function of a positive function is locally finite
support is asymptotically strictly monotonous.
-/
lemma logCounting_strictMono [ProperSpace E] {D : locallyFinsuppWithin (univ : Set E) ℤ} {e : E}
    (hD : single e ≤ D) :
    StrictMonoOn (logCounting D) (Ioi ‖e‖) := by
  rw [(by aesop : logCounting D = logCounting (single e) + logCounting (D - single e))]
  apply StrictMonoOn.add_monotone
  · intro a ha b hb hab
    rw [mem_Ioi] at ha hb
    rw [logCounting_single_eq_log_sub_const (e := e) ha.le, logCounting_single_eq_log_sub_const (e := e) hb.le]
    gcongr
    exact (norm_nonneg e).trans_lt ha
  · intro a ha b hb hab
    apply logCounting_mono _ _ ((norm_nonneg e).trans_lt hb) hab
    · simp [hD]
    · simpa [mem_Ioi] using (norm_nonneg e).trans_lt ha

/-!
## Asymptotic Behaviour of Logarithmic Counting Functions
-/

/--
A non-negative function with locally finite support is zero if and only if its
logarithmic counting functions is asymptotically bounded.
-/
lemma zero_iff_logCounting_bounded [ProperSpace E] {D : locallyFinsuppWithin (univ : Set E) ℤ}
    (h : 0 ≤ D) :
    D = 0 ↔ logCounting D =O[atTop] (1 : ℝ → ℝ) := by
  constructor
  · intro h₂
    simp [isBigO_of_le' (c := 0), h₂]
  · contrapose
    intro h₁
    obtain ⟨e, he⟩ := le_single (lt_of_le_of_ne h (h₁ ·.symm))
    rw [isBigO_iff'']
    push_neg
    intro a ha
    simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, norm_eq_abs, frequently_atTop,
      ge_iff_le]
    intro b
    obtain ⟨c, hc⟩ := eventually_atTop.1
      (isLittleO_iff.1 (one_isLittleO_logCounting_single (e := e)) ha)
    let ℓ := 1 + max ‖e‖ (max |b| |c|)
    have h₁ℓ : b < ℓ := by
      calc b
        _ ≤ |b| := le_abs_self _
        _ ≤ max |b| |c| := le_max_left _ _
        _ ≤ max ‖e‖ (max |b| |c|) := le_max_right _ _
        _ < 1 + max ‖e‖ (max |b| |c|) := lt_one_add _
        _ = ℓ := rfl
    have h₂ℓ : c < ℓ := by
      calc c
        _ ≤ |c| := le_abs_self _
        _ ≤ max |b| |c| := le_max_right _ _
        _ ≤ max ‖e‖ (max |b| |c|) := le_max_right _ _
        _ < 1 + max ‖e‖ (max |b| |c|) := lt_one_add _
        _ = ℓ := rfl
    have h₃ℓ : 1 ≤ ℓ := by simp [ℓ]
    have h₄ℓ : ℓ > ‖e‖ := by
      calc ‖e‖
        _ ≤ max ‖e‖ (max |b| |c|) := le_max_left _ _
        _ < 1 + max ‖e‖ (max |b| |c|) := lt_one_add _
        _ = ℓ := rfl
    use 1 + ℓ, h₁ℓ.le.trans (lt_one_add ℓ).le
    calc 1
      _ ≤ (a * |logCounting (single e) ℓ|) := by simpa [h₂ℓ.le] using hc ℓ
      _ ≤ (a * |logCounting D ℓ|) := by
        gcongr
        · apply logCounting_nonneg single_pos.le h₃ℓ
        · apply logCounting_le he h₃ℓ
      _ < a * |logCounting D (1 + ℓ)| := by
        gcongr 2
        rw [abs_of_nonneg (logCounting_nonneg h h₃ℓ),
          abs_of_nonneg (logCounting_nonneg h (le_add_of_nonneg_right (zero_le_one.trans h₃ℓ)))]
        apply logCounting_strictMono he h₄ℓ (h₄ℓ.trans (lt_one_add ℓ)) (lt_one_add ℓ)

end Function.locallyFinsuppWithin

namespace ValueDistribution

/-!
## Asymptotic Behaviour of Logarithmic Counting Functions
-/

/--
A meromorphic function has only removable singularities if and only if the
logarithmic counting function for its pole divisor is asymptotically bounded.
-/
theorem logCounting_isBigO_one_iff_analyticOnNhd {f : ℂ → ℂ} (h : Meromorphic f) :
    logCounting f ⊤ =O[atTop] (1 : ℝ → ℝ) ↔ AnalyticOnNhd ℂ (toMeromorphicNFOn f ⊤) ⊤ := by
  simp only [logCounting, reduceDIte, top_eq_univ]
  rw [← Function.locallyFinsuppWithin.zero_iff_logCounting_bounded (negPart_nonneg _)]
  constructor
  · intro h₁f z hz
    apply (meromorphicNFOn_toMeromorphicNFOn f ⊤
      trivial).meromorphicOrderAt_nonneg_iff_analyticAt.1
    rw [meromorphicOrderAt_toMeromorphicNFOn h.meromorphicOn (by trivial), ← WithTop.untop₀_nonneg,
      ← h.meromorphicOn.divisor_apply (by trivial), ← negPart_eq_zero,
      ← locallyFinsuppWithin.negPart_apply]
    aesop
  · intro h₁f
    rwa [negPart_eq_zero, ← h.meromorphicOn.divisor_of_toMeromorphicNFOn,
      (meromorphicNFOn_toMeromorphicNFOn _ _).divisor_nonneg_iff_analyticOnNhd]

end ValueDistribution
