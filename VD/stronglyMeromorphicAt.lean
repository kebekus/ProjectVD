import Mathlib.Analysis.Meromorphic.Basic
import VD.ToMathlib.NormalFormAt
import VD.meromorphicAt

open Topology

variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- TODO: MeromorphicNF is an open property
-- TODO: MeromorphicNF is a codiscrete property

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
    · simp only [Pi.smul_apply', smul_eq_mul, ne_eq, mul_eq_zero, not_or]
      exact smul_ne_zero h₂g h₂g_f
    · filter_upwards [h₃g_f]
      intro y hy
      simp [hy]
      exact smul_comm (g y) ((y - z₀) ^ n) (g_f y)

/- A function is strongly meromorphic at a point iff it is strongly meromorphic
   after multiplication with a non-vanishing analytic function
-/
theorem MeromorphicNFAt_of_mul_analytic
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

theorem MeromorphicNFAt.order_eq_zero_iff {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicNFAt f x) :
    hf.meromorphicAt.order = 0 ↔ f x ≠ 0 := by
  constructor
  · intro h₁f
    have h₂f := hf.analyticAt (le_of_eq h₁f.symm)
    apply h₂f.order_eq_zero_iff.1
    apply WithTopCoe
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

theorem MeromorphicNFAt.localIdentity
  {f g : 𝕜 → E}
  {x : 𝕜}
  (hf : MeromorphicNFAt f x)
  (hg : MeromorphicNFAt g x) :
  f =ᶠ[𝓝[≠] x] g ↔ f =ᶠ[𝓝 x] g := by
  constructor
  · intro h
    have t₀ := hf.meromorphicAt.order_congr h
    by_cases cs : hf.meromorphicAt.order = 0
    · rw [cs] at t₀
      exact (hf.analyticAt (le_of_eq cs.symm)).localIdentity (hg.analyticAt (le_of_eq t₀)) h
    · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE h
      let h₁f := cs
      rw [hf.order_eq_zero_iff] at h₁f
      let h₁g := cs
      rw [t₀, hg.order_eq_zero_iff] at h₁g
      simp_all
  · exact (Filter.EventuallyEq.filter_mono · nhdsWithin_le_nhds)
