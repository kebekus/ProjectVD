import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Algebra.Order.WithTop.Untop0

open scoped Interval Topology
open Real Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → 𝕜} {z₀ : 𝕜}

lemma untop₀_of_ne_top {a : WithTop ℤ} (ha : a ≠ ⊤) :
    a = a.untop₀ := by
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 ha
  simp [← hb]

theorem MeromorphicAt.order_ne_top_iff {f : 𝕜 → E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    hf.order ≠ ⊤ ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
      f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ (hf.order.untop₀) • g z :=
  ⟨fun h ↦ hf.order_eq_int_iff.1 (untop₀_of_ne_top h),
    fun h ↦ Option.ne_none_iff_exists'.2 ⟨hf.order.untopD 0, hf.order_eq_int_iff.2 h⟩⟩

theorem MeromorphicAt.order_pow (hf : MeromorphicAt f z₀) {n : ℕ} :
    (hf.pow n).order = n * hf.order := by
  induction' n with n hn
  · simp only [pow_zero, CharP.cast_eq_zero, zero_mul]
    rw [← WithTop.coe_zero, MeromorphicAt.order_eq_int_iff]
    use 1, analyticAt_const
    simp
  · simp only [pow_add, pow_one, (hf.pow n).order_mul hf, hn, Nat.cast_add, Nat.cast_one]
    cases hf.order
    · aesop
    · norm_cast
      simp only [Nat.cast_add, Nat.cast_one]
      ring

theorem MeromorphicAt.order_zpow (hf : MeromorphicAt f z₀) {n : ℤ} :
    (hf.zpow n).order = n * hf.order := by
  -- Trivial case: n = 0
  by_cases hn : n = 0
  · simp only [hn, zpow_zero, WithTop.coe_zero, zero_mul]
    rw [← WithTop.coe_zero, MeromorphicAt.order_eq_int_iff]
    use 1
    simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true, zpow_zero, smul_eq_mul, mul_one,
      eventually_true, and_self, and_true]
    apply analyticAt_const
  -- Trivial case: f locally zero
  by_cases h : hf.order = ⊤
  · simp only [h, ne_eq, WithTop.coe_eq_zero, hn, not_false_eq_true, WithTop.mul_top]
    rw [MeromorphicAt.order_eq_top_iff] at *
    filter_upwards [h]
    intro y hy
    simp [hy, zero_zpow n hn]
  -- General case
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.order_ne_top_iff.1 h
  rw [untop₀_of_ne_top h, ← WithTop.coe_mul, MeromorphicAt.order_eq_int_iff]
  use g ^ n, h₁g.zpow h₂g
  constructor
  · simp_all [zpow_eq_zero_iff hn]
  · filter_upwards [h₃g]
    intro y hy
    rw [Pi.pow_apply, hy, smul_eq_mul, mul_zpow]
    congr 1
    rw [mul_comm, zpow_mul]
