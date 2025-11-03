import VD.MathlibPending.Nevanlinna_counting_integral
import VD.MathlibPending.Nevanlinna_add_proximity

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution

variable
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f₁ f₂ : 𝕜 → E} {x : 𝕜}

/--
If `f₁` is meromorphic at `x`, then `f₁ + f₂` is meromorphic at `x` if and only
if `f₂` is meromorphic at `x`.
-/
theorem MeromorphicAt.meromorphicAt_iff_meromorphicAt_add
  (hf₁ : MeromorphicAt f₁ x) :
    MeromorphicAt f₂ x ↔ MeromorphicAt (f₁ + f₂) x := by
  exact ⟨fun _ ↦ by fun_prop, fun h ↦ by simpa using h.sub hf₁⟩

/--
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁
+ f₂` at `x` is the trailing coefficient of the function with the lowest order.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt {_ : 𝕜}
  (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ + f₂) x = meromorphicTrailingCoeffAt f₁ x := by
  -- Trivial case: f₁ not meromorphic at x
  by_cases hf₁ : ¬MeromorphicAt f₁ x
  · have : ¬MeromorphicAt (f₁ + f₂) x := by
      rwa [add_comm, ← hf₂.meromorphicAt_iff_meromorphicAt_add]
    simp_all
  rw [not_not] at hf₁
  -- Trivial case: f₂ vanishes locally around x
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · apply meromorphicTrailingCoeffAt_congr_nhdsNE
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₂ x to ℤ using h₁f₂ with n₂ hn₂
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  lift meromorphicOrderAt f₁ x to ℤ using (by aesop) with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  rw [WithTop.coe_lt_coe] at h
  have τ₀ : ∀ᶠ z in 𝓝[≠] x, (f₁ + f₂) z = (z - x) ^ n₁ • (g₁ + (z - x) ^ (n₂ - n₁) • g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with z h₁z h₂z h₃z
    simp only [Pi.add_apply, h₁z, h₂z, Pi.smul_apply, smul_add, ← smul_assoc, smul_eq_mul,
      add_right_inj]
    rw [← zpow_add₀, add_sub_cancel]
    simp_all [sub_ne_zero]
  have τ₁ : AnalyticAt 𝕜 (fun z ↦ g₁ z + (z - x) ^ (n₂ - n₁) • g₂ z) x :=
    h₁g₁.fun_add (AnalyticAt.fun_smul (AnalyticAt.fun_zpow_nonneg (by fun_prop)
      (sub_nonneg_of_le h.le)) h₁g₂)
  have τ₂ : g₁ x + (x - x) ^ (n₂ - n₁) • g₂ x ≠ 0 := by
    simp_all [zero_zpow _ (sub_ne_zero.2 (ne_of_lt h).symm)]
  rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁,
    τ₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE τ₂ τ₀, sub_self, add_eq_left, smul_eq_zero,
    zero_zpow _ (sub_ne_zero.2 (ne_of_lt h).symm)]
  tauto

/--
If `f₁` and `f₂` have equal order at `x` and if their trailing coefficients do
not cancel, then the trailing coefficient of `f₁ + f₂` at `x` is the sum of the
trailing coefficients.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add
  (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
  (h₁ : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x)
  (h₂ : meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x ≠ 0) :
    meromorphicTrailingCoeffAt (f₁ + f₂) x = meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x := by
  -- Trivial case: f₁ vanishes locally around x
  by_cases h₁f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [meromorphicTrailingCoeffAt_of_order_eq_top h₁f₁, zero_add]
    apply meromorphicTrailingCoeffAt_congr_nhdsNE
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₁]
    simp
  -- General case
  lift meromorphicOrderAt f₁ x to ℤ using (by aesop) with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  lift meromorphicOrderAt f₂ x to ℤ using (by aesop) with n₂ hn₂
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  rw [WithTop.coe_eq_coe, h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁,
    h₁g₂.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₂ h₃g₂] at *
  have τ₀ : ∀ᶠ z in 𝓝[≠] x, (f₁ + f₂) z = (z - x) ^ n₁ • (g₁ + g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with z h₁z h₂z h₃z
    simp_all
  simp [AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (by fun_prop) (by simp_all) τ₀]
