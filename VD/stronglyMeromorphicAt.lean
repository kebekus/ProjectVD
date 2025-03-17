import Mathlib.Analysis.Meromorphic.NormalFormAt
import Mathlib.Analysis.Analytic.IsolatedZeros

open Filter Topology

variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Local identity theorem: two analytic functions agree on a punctured
neighborhood iff they agree on a neighborhood.

See `MeromorphicNFAt.eventuallyEq_nhdNE_iff_eventuallyEq_nhd` for the analogous
statement for meromorphic functions in normal form.
-/
theorem AnalyticAt.eventuallyEq_nhdNE_iff_eventuallyEq_nhd {f g : 𝕜 → E} {z₀ : 𝕜}
    (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    f =ᶠ[𝓝[≠] z₀] g ↔ f =ᶠ[𝓝 z₀] g := by
  constructor
  · intro hfg
    rcases ((hf.sub hg).eventually_eq_zero_or_eventually_ne_zero) with h | h
    · exact Filter.eventuallyEq_iff_sub.2 h
    · simpa using (Filter.eventually_and.2 ⟨Filter.eventuallyEq_iff_sub.mp hfg, h⟩).exists
  · exact (Filter.EventuallyEq.filter_mono · nhdsWithin_le_nhds)

/-- Meromorphic functions that agree in a punctured neighborhood of `z₀` have the same order at
`z₀`. -/
theorem MeromorphicAt.order_congr {f₁ f₂ : 𝕜 → E} {z₀ : 𝕜} (hf₁ : MeromorphicAt f₁ z₀)
    (hf₁₂ : f₁ =ᶠ[𝓝[≠] z₀] f₂):
    hf₁.order = (hf₁.congr hf₁₂).order := by
  by_cases h₁f₁ : hf₁.order = ⊤
  · rw [h₁f₁, eq_comm, (hf₁.congr hf₁₂).order_eq_top_iff]
    rw [hf₁.order_eq_top_iff] at h₁f₁
    exact EventuallyEq.rw h₁f₁ (fun x => Eq (f₂ x)) hf₁₂.symm
  · obtain ⟨n, hn : hf₁.order = n⟩ := Option.ne_none_iff_exists'.mp h₁f₁
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (hf₁.order_eq_int_iff n).1 hn
    rw [hn, eq_comm, (hf₁.congr hf₁₂).order_eq_int_iff]
    use g, h₁g, h₂g
    exact EventuallyEq.rw h₃g (fun x => Eq (f₂ x)) hf₁₂.symm

/-- Meromorphic functions are analytic outside of a discrete subset in the domain of
meromorphicity. -/
theorem MeromorphicOn.analyticAt_codiscreteWithin [CompleteSpace E] {f : 𝕜 → E} {U : Set 𝕜}
    (hf : MeromorphicOn f U) :
    { x | AnalyticAt 𝕜 f x } ∈ Filter.codiscreteWithin U := by
  rw [mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right, ← Filter.eventually_mem_set]
  apply (hf x hx).eventually_analyticAt.mono
  simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_setOf_eq, not_and, not_not]
  tauto

/-- Meromorphic functions have normal form outside of a discrete subset in the domain of
meromorphicity. -/
theorem MeromorphicOn.meromorphicNFAt_codiscreteWithin [CompleteSpace E] {f : 𝕜 → E} {U : Set 𝕜}
    (hf : MeromorphicOn f U) :
    { x | MeromorphicNFAt f x } ∈ Filter.codiscreteWithin U := by
  filter_upwards [hf.analyticAt_codiscreteWithin] with _ ha
  exact ha.meromorphicNFAt

/-- Helper lemma for `meromorphicNFAt_iff_meromorphicNFAt_of_smul_analytic`: if
`f` is meromorphic in normal form at `z₀` and `g` is analytic without zero at
`z₀`, then `g • f` is meromorphic in normal form at `z₀`. -/
lemma MeromorphicNFAt.meromorphicNFAt_of_smul_analytic {f : 𝕜 → E} {g : 𝕜 → 𝕜} {z₀ : 𝕜}
    (hf : MeromorphicNFAt f z₀) (h₁g : AnalyticAt 𝕜 g z₀) (h₂g : g z₀ ≠ 0) :
    MeromorphicNFAt (g • f) z₀ := by
  rcases hf with h₁f | ⟨n, g_f, h₁g_f, h₂g_f, h₃g_f⟩
  · left
    filter_upwards [h₁f]
    simp_all
  · right
    use n, g • g_f, h₁g.smul h₁g_f
    constructor
    · simp [smul_ne_zero h₂g h₂g_f]
    · filter_upwards [h₃g_f]
      intro y hy
      simp [hy, smul_comm (g y) ((y - z₀) ^ n) (g_f y)]

/-- If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in
normal form at `z₀` iff `g • f` is meromorphic in normal form at `z₀`. -/
theorem meromorphicNFAt_iff_meromorphicNFAt_of_smul_analytic
    {g : 𝕜 → 𝕜}
    {f : 𝕜 → E}
    {z₀ : 𝕜}
    (h₁g : AnalyticAt 𝕜 g z₀)
    (h₂g : g z₀ ≠ 0) :
    MeromorphicNFAt f z₀ ↔ MeromorphicNFAt (g • f) z₀ := by
  constructor
  · exact fun hf ↦ hf.meromorphicNFAt_of_smul_analytic h₁g h₂g
  · intro hprod
    have : f =ᶠ[𝓝 z₀] g⁻¹ • g • f := by
      filter_upwards [h₁g.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr h₂g)]
      intro y hy
      rw [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_singleton_iff] at hy
      simp [hy]
    rw [meromorphicNFAt_congr this]
    exact hprod.meromorphicNFAt_of_smul_analytic (h₁g.inv h₂g) (inv_ne_zero h₂g)

/-- If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in
normal form at `z₀` iff `g * f` is meromorphic in normal form at `z₀`. -/
theorem meromorphicNFAt_iff_meromorphicNFAt_of_mul_analytic
    {f g : 𝕜 → 𝕜}
    {z₀ : 𝕜}
    (h₁g : AnalyticAt 𝕜 g z₀)
    (h₂g : g z₀ ≠ 0) :
    MeromorphicNFAt f z₀ ↔ MeromorphicNFAt (g * f) z₀ := by
  rw [← smul_eq_mul]
  exact meromorphicNFAt_iff_meromorphicNFAt_of_smul_analytic h₁g h₂g

/- Private helper lemma. -/
private lemma WithTop.map_natCast_eq_zero {n : WithTop ℕ}
  (hn : WithTop.map (Nat.cast : ℕ → ℤ) n = 0) :
  n = 0 := by
  rcases n
  · contradiction
  · simp only [WithTop.map, Option.map] at hn
    rw [Int.ofNat_eq_zero.mp (WithTop.coe_eq_zero.mp hn)]
    rfl

/-- If `f` is meromorphic in normal form at `z₀`, then `f` has order zero iff it
does not vanish at `z₀`. -/
theorem MeromorphicNFAt.order_eq_zero_iff {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicNFAt f x) :
    hf.meromorphicAt.order = 0 ↔ f x ≠ 0 := by
  constructor
  · intro h₁f
    have h₂f := hf.order_nonneg_iff_analyticAt.1 (le_of_eq h₁f.symm)
    apply h₂f.order_eq_zero_iff.1
    apply WithTop.map_natCast_eq_zero
    rwa [h₂f.meromorphicAt_order] at h₁f
  · intro h
    have hf' := hf
    rcases hf with h₁ | ⟨n, g, h₁g, h₂g, h₃g⟩
    · have := h₁.eq_of_nhds
      tauto
    · have : n = 0 := by
        by_contra hContra
        have := Filter.EventuallyEq.eq_of_nhds h₃g
        simp only [Pi.smul_apply', Pi.pow_apply, sub_self, zero_zpow n hContra, zero_smul] at this
        tauto
      simp only [this, zpow_zero, smul_eq_mul, one_mul] at h₃g
      apply (hf'.meromorphicAt.order_eq_int_iff 0).2
      use g, h₁g, h₂g
      simp only [zpow_zero, smul_eq_mul, one_mul]
      exact h₃g.filter_mono nhdsWithin_le_nhds

/-- Local identity theorem: two meromorphic functions in normal form agree in a
neighborhood iff they agree in a pointed neighborhood.

See `AnalytivAt.eventuallyEq_nhdNE_iff_eventuallyEq_nhd` for the analogous
statement for analytic functions.
-/
theorem MeromorphicNFAt.eventuallyEq_nhdNE_iff_eventuallyEq_nhd {f g : 𝕜 → E} {z₀ : 𝕜}
    (hf : MeromorphicNFAt f z₀) (hg : MeromorphicNFAt g z₀) :
    f =ᶠ[𝓝[≠] z₀] g ↔ f =ᶠ[𝓝 z₀] g := by
  constructor
  · intro h
    have t₀ := hf.meromorphicAt.order_congr h
    by_cases cs : hf.meromorphicAt.order = 0
    · rw [cs] at t₀
      have Z := (hf.order_nonneg_iff_analyticAt.1 (le_of_eq cs.symm))
      have W := hg.order_nonneg_iff_analyticAt.1 (le_of_eq t₀)
      exact (AnalyticAt.eventuallyEq_nhdNE_iff_eventuallyEq_nhd Z W).1 h
    · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE h
      let h₁f := cs
      rw [hf.order_eq_zero_iff] at h₁f
      let h₁g := cs
      rw [t₀, hg.order_eq_zero_iff] at h₁g
      simp only [not_not] at *
      rw [h₁f, h₁g]
  · exact (Filter.EventuallyEq.filter_mono · nhdsWithin_le_nhds)
