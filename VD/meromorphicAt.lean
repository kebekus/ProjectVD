import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import VD.mathlibAddOn

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → 𝕜} {z₀ : 𝕜}

-- TODO: AnalyticAt is a codiscrete property within MeromorphicAt

theorem MeromorphicAt.order_ne_top_iff {f : 𝕜 → E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    hf.order ≠ ⊤ ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ (hf.order.untopD 0) • g z :=
  ⟨fun h ↦ hf.order_eq_int_iff.1 (untop'_of_ne_top h).symm,
    fun h ↦ Option.ne_none_iff_exists'.2 ⟨hf.order.untopD 0, hf.order_eq_int_iff.2 h⟩⟩

theorem MeromorphicAt.order_pow (hf : MeromorphicAt f z₀) {n : ℕ} :
    (hf.pow n).order = n * hf.order := by
  induction' n with n hn
  · simp
    rw [← WithTop.coe_zero, MeromorphicAt.order_eq_int_iff]
    use 1, analyticAt_const
    simp
  · simp [add_mul, pow_add, (hf.pow n).order_mul hf, hn]
    cases hf.order
    · rw [add_top]
      rfl
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
  · rw [h]
    simp [hn]
    rw [MeromorphicAt.order_eq_top_iff]
    rw [MeromorphicAt.order_eq_top_iff] at h
    filter_upwards [h]
    intro y hy
    simp [hy]
    exact zero_zpow n hn
  -- General case
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.order_ne_top_iff.1 h
  have : ↑n * hf.order = ↑(n * (WithTop.untopD 0 hf.order)) := by
    rw [WithTop.coe_mul]
    congr
    exact (untop'_of_ne_top h).symm
  rw [this,]
  rw [MeromorphicAt.order_eq_int_iff]
  use g ^ n, h₁g.zpow h₂g
  constructor
  · simp only [Pi.pow_apply, ne_eq]
    rwa [zpow_eq_zero_iff hn]
  · filter_upwards [h₃g]
    intro y hy
    rw [Pi.pow_apply, hy, smul_eq_mul, mul_zpow]
    congr 1
    rw [mul_comm, zpow_mul]

theorem meromorphicAt_congr'
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → E} {x : 𝕜}
  (h : f =ᶠ[𝓝 x] g) : MeromorphicAt f x ↔ MeromorphicAt g x :=
  MeromorphicAt.meromorphicAt_congr (Filter.EventuallyEq.filter_mono h nhdsWithin_le_nhds)

-- Might want to think about adding an analytic function instead of a constant
theorem MeromorphicAt.order_add_const
  --have {z : ℂ} : 0 < (hf z trivial).order → (hf z trivial).order = ((hf.add (MeromorphicOn.const a)) z trivial).order:= by
  {f : ℂ → ℂ}
  {z a : ℂ}
  (hf : MeromorphicAt f z) :
  hf.order < 0 → hf.order = (hf.add (MeromorphicAt.const a z)).order := by
  intro h

  by_cases ha: a = 0
  · -- might want theorem MeromorphicAt.order_const
    have : (MeromorphicAt.const a z).order = ⊤ := by
      rw [MeromorphicAt.order_eq_top_iff]
      rw [ha]
      simp
    rw [hf.order_add_of_unequal_order (MeromorphicAt.const a z)]
    rw [this]
    simp
    rw [this]
    exact h.ne_top
  · have : (MeromorphicAt.const a z).order = (0 : ℤ) := by
      rw [MeromorphicAt.order_eq_int_iff]
      use fun _ ↦ a
      exact ⟨analyticAt_const, by simpa⟩
    rw [hf.order_add_of_unequal_order (MeromorphicAt.const a z)]
    rw [this]
    simp [h.le]
    rw [this]
    exact h.ne
