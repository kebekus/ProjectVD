import Mathlib.Analysis.Meromorphic.Divisor

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → 𝕜} {z₀ : 𝕜}


/--
If two functions agree in a punctured neighborhood, then one if meromorphic iff
the other is meromorphic.
-/
theorem meromorphicAt_congr
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → E} {x : 𝕜}
  (h : f =ᶠ[𝓝[≠] x] g) : MeromorphicAt f x ↔ MeromorphicAt g x :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩

/--
When seen as meromorphic functions, analytic functions have nonnegative order.
-/
theorem AnalyticAt.meromorphicAt_order_nonneg
  {f : 𝕜 → E}
  {z₀ : 𝕜}
  (hf : AnalyticAt 𝕜 f z₀) :
  0 ≤ hf.meromorphicAt.order := by
  rw [hf.meromorphicAt_order, (by rfl : (0 : WithTop ℤ) = WithTop.map Nat.cast (0 : ℕ∞))]
  simp

/--
The order of a sum at least the minimum of the orders of the summands.
-/
theorem MeromorphicAt.order_add {f₁ f₂ : 𝕜 → E} {z₀ : 𝕜} (hf₁ : MeromorphicAt f₁ z₀)
    (hf₂ : MeromorphicAt f₂ z₀) :
    min hf₁.order hf₂.order ≤ (hf₁.add hf₂).order := by
  -- Handle the trivial cases where one of the orders equals ⊤
  by_cases h₂f₁: hf₁.order = ⊤
  · simp only [h₂f₁, le_top, inf_of_le_right]
    rw [(hf₁.add hf₂).order_congr]
    filter_upwards [hf₁.order_eq_top_iff.1 h₂f₁]
    simp
  by_cases h₂f₂: hf₂.order = ⊤
  · simp only [h₂f₂, le_top, inf_of_le_left]
    rw [(hf₁.add hf₂).order_congr]
    filter_upwards [hf₂.order_eq_top_iff.1 h₂f₂]
    simp
  -- General case
  lift hf₁.order to ℤ using h₂f₁ with n₁ hn₁
  lift hf₂.order to ℤ using h₂f₂ with n₂ hn₂
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (hf₁.order_eq_int_iff n₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (hf₂.order_eq_int_iff n₂).1 hn₂.symm
  let n := min n₁ n₂
  let g := (fun z ↦ (z - z₀) ^ (n₁ - n)) • g₁ +  (fun z ↦ (z - z₀) ^ (n₂ - n)) • g₂
  have h₁g : AnalyticAt 𝕜 g z₀ := by
    apply AnalyticAt.add
    apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (Int.min_le_left n₁ n₂))).smul h₁g₁
    apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (Int.min_le_right n₁ n₂))).smul h₁g₂
  have : f₁ + f₂ =ᶠ[𝓝[≠] z₀] ((· - z₀) ^ n) • g := by
    filter_upwards [h₃g₁, h₃g₂, (self_mem_nhdsWithin : {z₀}ᶜ ∈ 𝓝[≠] z₀)]
    unfold g
    simp_all [smul_add, ← smul_assoc, ← zpow_add', sub_ne_zero]
  have t₀ : MeromorphicAt ((·  - z₀) ^ n) z₀ := by fun_prop
  have t₁ : t₀.order = n := by
    rw [t₀.order_eq_int_iff]
    use 1, analyticAt_const
    simp
  rw [(hf₁.add hf₂).order_congr this, t₀.order_smul h₁g.meromorphicAt, t₁]
  exact le_add_of_nonneg_right h₁g.meromorphicAt_order_nonneg

/--
Helper lemma for MeromorphicAt.order_add_of_unequal_order.
-/
lemma MeromorphicAt.order_add_of_order_lt_order {f₁ f₂ : 𝕜 → E} {z₀ : 𝕜} (hf₁ : MeromorphicAt f₁ z₀)
    (hf₂ : MeromorphicAt f₂ z₀) (h : hf₁.order < hf₂.order) :
    (hf₁.add hf₂).order = hf₁.order := by
  -- Trivial case: f₂ vanishes identically around z₀
  by_cases h₁f₂ : hf₂.order = ⊤
  · rw [(hf₁.add hf₂).order_congr]
    filter_upwards [hf₂.order_eq_top_iff.1 h₁f₂]
    simp
  -- General case
  lift hf₂.order to ℤ using h₁f₂ with n₂ hn₂
  lift hf₁.order to ℤ using h.ne_top with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (hf₁.order_eq_int_iff n₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (hf₂.order_eq_int_iff n₂).1 hn₂.symm
  rw [(hf₁.add hf₂).order_eq_int_iff n₁]
  use g₁ + (· - z₀) ^ (n₂ - n₁) • g₂
  constructor
  · apply h₁g₁.add (AnalyticAt.smul _ h₁g₂)
    apply AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (Int.le_of_lt (WithTop.coe_lt_coe.1 h)))
  constructor
  · have : (0 : 𝕜) ^ (n₂ - n₁) = (0 : 𝕜) := by
      rw [zpow_eq_zero_iff]
      rw [ne_eq, sub_eq_zero, eq_comm, ← ne_eq]
      exact ne_of_lt (WithTop.coe_lt_coe.1 h)
    simpa [this]
  · filter_upwards [h₃g₁, h₃g₂, (self_mem_nhdsWithin : {z₀}ᶜ ∈ 𝓝[≠] z₀)]
    simp_all [smul_add, ← smul_assoc, ← zpow_add', sub_ne_zero]

/--
If two meromorphic functions have unequal orders, then the order of their sum is
exactly the minimum of the orders of the summands.
-/
theorem MeromorphicAt.order_add_of_unequal_order {f₁ f₂ : 𝕜 → E} {z₀ : 𝕜} (hf₁ : MeromorphicAt f₁ z₀)
    (hf₂ : MeromorphicAt f₂ z₀) (h : hf₁.order ≠ hf₂.order) :
    (hf₁.add hf₂).order = min hf₁.order hf₂.order := by
  by_cases h₁ : hf₁.order < hf₂.order
  · rw [min_eq_left (le_of_lt h₁)]
    exact hf₁.order_add_of_order_lt_order hf₂ h₁
  · rw [min_eq_right (le_of_not_lt h₁)]
    simp_rw [AddCommMagma.add_comm f₁ f₂]
    exact hf₂.order_add_of_order_lt_order hf₁ (lt_of_le_of_ne (le_of_not_lt h₁) h.symm)
