import Mathlib.Analysis.Analytic.Order

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f₁ f₂ : 𝕜 → E} {z₀ : 𝕜}

/-- If two functions agree in a neighborhood of `z₀`, then their orders at `z₀` agree. -/
theorem AnalyticAt.order_congr (hf₁ : AnalyticAt 𝕜 f₁ z₀) (h : f₁ =ᶠ[𝓝 z₀] f₂):
    (hf₁.congr h).order = hf₁.order := by
  -- Trivial case: f vanishes identially around z₀
  by_cases h₁f₁ : hf₁.order = ⊤
  · rw [h₁f₁, order_eq_top_iff]
    filter_upwards [hf₁.order_eq_top_iff.1 h₁f₁, h]
    intro a h₁a h₂a
    rwa [← h₂a]
  -- General case
  lift hf₁.order to ℕ using h₁f₁ with n hn
  rw [eq_comm] at hn
  rw [AnalyticAt.order_eq_nat_iff] at *
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := hn
  use g, h₁g, h₂g
  filter_upwards [h, h₃g]
  intro a h₁a h₂a
  rw [← h₂a, h₁a]

/-- The hpow of an analytic function is analytic -/
@[fun_prop]
lemma AnalyticAt.hpow {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) :
    AnalyticAt 𝕜 (HPow.hPow f n) z₀ := by apply hf.pow

/-- The hpow of an analytic function is analytic -/
@[fun_prop]
lemma AnalyticAt.fun_hpow  {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) :
    AnalyticAt 𝕜 (fun z ↦ HPow.hPow (f z) n) z₀ := by apply hf.pow

/-- Helper lemma, required to state analyticAt_order_centeredMonomial below -/
lemma analyticAt_centeredMonomial (z₀ : 𝕜) (n : ℕ) :
    AnalyticAt 𝕜 ((· - z₀) ^ n) z₀ := by fun_prop

/-- Simplifier lemma for the order of a centered monomial -/
@[simp]
lemma analyticAt_order_centeredMonomial {z₀ : 𝕜} {n : ℕ} :
    (analyticAt_centeredMonomial z₀ n).order = n := by
  rw [AnalyticAt.order_eq_nat_iff]
  use 1
  simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true, Pi.pow_apply, smul_eq_mul,
    mul_one, eventually_true, and_self, and_true]
  exact analyticAt_const

--------------------------

/-- Helper lemma for `AnalyticAt.order_smul` -/
lemma AnalyticAt.order_smul_of_order_eq_top₁ {f : 𝕜 → 𝕜} {g : 𝕜 → E} (hf : AnalyticAt 𝕜 f z₀)
    (hg : AnalyticAt 𝕜 g z₀) (h₁f : hf.order = ⊤) :
    (hf.smul hg).order = ⊤ := by
  rw [AnalyticAt.order_eq_top_iff] at *
  filter_upwards [h₁f]
  exact fun _ ha ↦ by simp [ha]

/-- Helper lemma for `AnalyticAt.order_smul` -/
lemma AnalyticAt.order_smul_of_order_eq_top₂ {f : 𝕜 → 𝕜} {g : 𝕜 → E} (hf : AnalyticAt 𝕜 f z₀)
    (hg : AnalyticAt 𝕜 g z₀) (h₁g : hg.order = ⊤) :
    (hf.smul hg).order = ⊤ := by
  rw [AnalyticAt.order_eq_top_iff] at *
  filter_upwards [h₁g]
  exact fun _ ha ↦ by simp [ha]

/-- The order is additive when scalar multiplying analytic functions. -/
theorem AnalyticAt.order_smul {f : 𝕜 → 𝕜} {g : 𝕜 → E} (hf : AnalyticAt 𝕜 f z₀)
    (hg : AnalyticAt 𝕜 g z₀) :
    (hf.smul hg).order = hf.order + hg.order := by
  -- Trivial cases: one of the functions vanishes around z₀
  by_cases h₂f : hf.order = ⊤
  · simp [hf.order_smul_of_order_eq_top₁ hg h₂f, h₂f]
  by_cases h₂g : hg.order = ⊤
  · simp [hf.order_smul_of_order_eq_top₂ hg h₂g, h₂g]
  -- Non-trivial case: both functions do not vanish around z₀
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := hf.order_ne_top_iff.1 h₂f
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := hg.order_ne_top_iff.1 h₂g
  rw [← ENat.coe_toNat h₂f, ← ENat.coe_toNat h₂g, ← ENat.coe_add, (hf.smul hg).order_eq_nat_iff]
  use g₁ • g₂, by exact h₁g₁.smul h₁g₂
  constructor
  · simp only [Pi.smul_apply', ne_eq, smul_eq_zero, not_or]
    tauto
  · filter_upwards [h₃g₁, h₃g₂]
    intro a h₁a h₂a
    rw [Pi.smul_apply', Pi.smul_apply', h₂a, ← smul_assoc, ← smul_assoc]
    congr 1
    rw [h₁a, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring

--------------------------

/-- Helper lemma for AnalyticAt.order_add: adding a locally vanishing function does not
affect the order. -/
lemma AnalyticAt.order_add_top (hf₁ : AnalyticAt 𝕜 f₁ z₀) (hf₂ : AnalyticAt 𝕜 f₂ z₀)
    (h : hf₂.order = ⊤) :
    (hf₁.add hf₂).order = hf₁.order := by
  apply AnalyticAt.order_congr hf₁
  filter_upwards [hf₂.order_eq_top_iff.1 h]
  intro a h₁a
  simp [h₁a]

/-- The order of a sub at least the minimum of the orders of the summands. -/
theorem AnalyticAt.order_add (hf₁ : AnalyticAt 𝕜 f₁ z₀) (hf₂ : AnalyticAt 𝕜 f₂ z₀) :
    min hf₁.order hf₂.order ≤ (hf₁.add hf₂).order := by
  -- Trivial case: f₁ vanishes identically around z₀
  by_cases h₁f₁ : hf₁.order = ⊤
  · rw [h₁f₁]
    simp only [le_top, inf_of_le_right]
    simp_rw [AddCommMagma.add_comm f₁ f₂]
    rw [AnalyticAt.order_add_top hf₂ hf₁ h₁f₁]
  -- Trivial case: f₂ vanishes identically around z₀
  by_cases h₁f₂ : hf₂.order = ⊤
  · rw [h₁f₂]
    simp only [le_top, inf_of_le_left]
    rw [AnalyticAt.order_add_top hf₁ hf₂ h₁f₂]
  -- General case
  lift hf₁.order to ℕ using h₁f₁ with n₁ hn₁
  lift hf₂.order to ℕ using h₁f₂ with n₂ hn₂
  rw [eq_comm, AnalyticAt.order_eq_nat_iff] at *
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := hn₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := hn₂
  let m := min n₁ n₂
  let G := fun z ↦ (z - z₀) ^ (n₁ - m) • g₁ z + (z - z₀) ^ (n₂ - m) • g₂ z
  have hG : AnalyticAt 𝕜 G z₀ := by fun_prop
  have : f₁ + f₂ =ᶠ[𝓝 z₀] (· - z₀) ^ m • G := by
    dsimp [G]
    filter_upwards [h₃g₁, h₃g₂]
    intro a h₁a h₂a
    simp [h₁a, h₂a]
    congr 1
    repeat
      simp [← smul_assoc, smul_eq_mul, ← pow_add, m]
  rw [← (hf₁.add hf₂).order_congr this, AnalyticAt.order_smul _ hG,
    analyticAt_order_centeredMonomial]
  simp only [m, G]
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
  use g₁ + (· - z₀) ^ (n₂ - n₁) • g₂
  constructor
  · apply h₁g₁.add
    apply AnalyticAt.smul _ h₁g₂
    apply AnalyticAt.pow
    fun_prop
  · constructor
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
