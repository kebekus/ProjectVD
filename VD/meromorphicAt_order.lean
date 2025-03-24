import Mathlib.Analysis.Meromorphic.Order
import VD.meromorphicAt

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f₁ f₂ : 𝕜 → E} {z₀ : 𝕜}


--------------------------

/-- Helper lemma, required to state analyticAt_order_centeredMonomial below -/
lemma meromorphicAt_centeredMonomial (z₀ : 𝕜) (n : ℤ) :
    MeromorphicAt ((· - z₀) ^ n) z₀ := by fun_prop

/-- Simplifier lemma for the order of a centered monomial -/
@[simp]
lemma meromorphicAt_order_centeredMonomial {z₀ : 𝕜} {n : ℤ} :
    (meromorphicAt_centeredMonomial z₀ n).order = n := by
  rw [MeromorphicAt.order_eq_int_iff]
  use 1
  simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true, Pi.pow_apply, smul_eq_mul,
    mul_one, eventually_true, and_self, and_true]
  exact analyticAt_const

--------------------------

/-- Helper lemma for AnalyticAt.order_add: adding a locally vanishing function does not
affect the order. -/
lemma MeromorphicAt.order_add_top (hf₁ : MeromorphicAt f₁ z₀) (hf₂ : MeromorphicAt f₂ z₀)
    (h : hf₂.order = ⊤) :
    (hf₁.add hf₂).order = hf₁.order := by
  rw [eq_comm]
  apply hf₁.order_congr
  filter_upwards [hf₂.order_eq_top_iff.1 h]
  intro a h₁a
  simp [h₁a]

/-- The order of a sub at least the minimum of the orders of the summands. -/
theorem MermomorphicAt.order_add (hf₁ : MeromorphicAt f₁ z₀) (hf₂ : MeromorphicAt f₂ z₀) :
    min hf₁.order hf₂.order ≤ (hf₁.add hf₂).order := by
  -- Trivial case: f₁ vanishes identically around z₀
  by_cases h₁f₁ : hf₁.order = ⊤
  · rw [h₁f₁]
    simp only [le_top, inf_of_le_right]
    simp_rw [AddCommMagma.add_comm f₁ f₂]
    rw [MeromorphicAt.order_add_top hf₂ hf₁ h₁f₁]
  -- Trivial case: f₂ vanishes identically around z₀
  by_cases h₁f₂ : hf₂.order = ⊤
  · rw [h₁f₂]
    simp only [le_top, inf_of_le_left]
    rw [MeromorphicAt.order_add_top hf₁ hf₂ h₁f₂]
  -- General case
  lift hf₁.order to ℤ using h₁f₁ with n₁ hn₁
  lift hf₂.order to ℤ using h₁f₂ with n₂ hn₂
  rw [eq_comm, MeromorphicAt.order_eq_int_iff] at *
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := hn₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := hn₂
  let m := min n₁ n₂
  let G := fun z ↦ (z - z₀) ^ (n₁ - m) • g₁ z + (z - z₀) ^ (n₂ - m) • g₂ z
  have hG : AnalyticAt 𝕜 G z₀ := by
    apply AnalyticAt.add
    apply AnalyticAt.smul _ h₁g₁
    apply AnalyticAt.fun_zpow_nonneg
    fun_prop
    rw [sub_nonneg]
    exact Int.min_le_left n₁ n₂
    apply AnalyticAt.smul _ h₁g₂
    apply AnalyticAt.fun_zpow_nonneg
    fun_prop
    rw [sub_nonneg]
    exact Int.min_le_right n₁ n₂
  have : f₁ + f₂ =ᶠ[𝓝[≠] z₀] (· - z₀) ^ m • G := by
    dsimp [G]
    filter_upwards [h₃g₁, h₃g₂]
    intro a h₁a h₂a
    simp only [Pi.add_apply, h₁a, h₂a, Pi.smul_apply', Pi.pow_apply, smul_add, G]
    congr 1
    simp [← smul_assoc, smul_eq_mul, ← zpow_add, m]
    sorry

  rw [(hf₁.add hf₂).order_congr this, MeromorphicAt.order_smul _ hG.meromorphicAt,
    meromorphicAt_order_centeredMonomial]
  simp only [m, G, ← WithTop.coe_min]
  by_cases h₁G : hG.order = ⊤
  · simp [hG.meromorphicAt_order, h₁G]
  · have : hG.meromorphicAt.order ≠ ⊤ := by
      sorry
    lift hG.meromorphicAt.order to ℤ using this with n hn
    rw [← WithTop.coe_add]
    rw [WithTop.le_coe_iff]
    simp
    rw [hG.meromorphicAt_order, ← hn]

    sorry

  exact le_self_add

/-- Helper lemma for AnalyticAt.order_add_of_unequal_order -/
lemma AnalyticAt.order_add_of_order_lt_order (hf₁ : AnalyticAt 𝕜 f₁ z₀) (hf₂ : AnalyticAt 𝕜 f₂ z₀)
    (h : hf₁.order < hf₂.order) :
    (hf₁.add hf₂).order = hf₁.order := by
  -- Trivial case: f₂ vanishes identically around z₀
  by_cases h₁f₂ : hf₂.order = ⊤
  · apply AnalyticAt.order_congr hf₁
    filter_upwards [hf₂.order_eq_top_iff.1 h₁f₂]
    intro a h₁a
    simp [h₁a]
  -- General case
  lift hf₂.order to ℕ using h₁f₂ with n₂ hn₂
  lift hf₁.order to ℕ using h.ne_top with n₁ hn₁
  rw [Nat.cast_lt] at h
  rw [eq_comm] at hn₁ hn₂
  rw [AnalyticAt.order_eq_nat_iff] at *
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := hn₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := hn₂
  use g₁ + (· - z₀) ^ (n₂ - n₁) • g₂, by fun_prop
  constructor
  · simpa [Nat.sub_ne_zero_iff_lt.mpr h]
  · filter_upwards [h₃g₁, h₃g₂]
    intro a h₁a h₂a
    simp only [Pi.add_apply, h₁a, h₂a, Pi.smul_apply', Pi.pow_apply, smul_add, ← smul_assoc,
      smul_eq_mul, add_right_inj]
    rw [← pow_add, add_comm, eq_comm, Nat.sub_add_cancel (Nat.le_of_succ_le h)]

/-- If two functions have unequal orders, then the order of their sum is exactly the minimum
of the orders of the summands. -/
theorem AnalyticAt.order_add_of_unequal_order (hf₁ : AnalyticAt 𝕜 f₁ z₀) (hf₂ : AnalyticAt 𝕜 f₂ z₀)
    (h : hf₁.order ≠ hf₂.order) :
    (hf₁.add hf₂).order = min hf₁.order hf₂.order := by
  by_cases h₁ : hf₁.order < hf₂.order
  · rw [min_eq_left (le_of_lt h₁)]
    exact hf₁.order_add_of_order_lt_order hf₂ h₁
  · rw [min_eq_right (le_of_not_lt h₁)]
    simp_rw [AddCommMagma.add_comm f₁ f₂]
    exact hf₂.order_add_of_order_lt_order hf₁ (lt_of_le_of_ne (le_of_not_lt h₁) h.symm)
