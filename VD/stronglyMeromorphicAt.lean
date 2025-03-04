import Mathlib.Analysis.Meromorphic.Basic
import VD.NormalFormAt

open Topology

variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- TODO: MeromorphicNF is an open property
-- TODO: MeromorphicNF is a codiscrete property

lemma MeromorphicNFAt_of_mul_analytic'
  {f : 𝕜 → 𝕜}
  {g : 𝕜 → 𝕜}
  {z₀ : 𝕜}
  (h₁g : AnalyticAt 𝕜 g z₀)
  (h₂g : g z₀ ≠ 0) :
  MeromorphicNFAt f z₀ → MeromorphicNFAt (f • g) z₀ := by

  intro hf
  --unfold MeromorphicNFAt at hf
  rcases hf with h₁f|h₁f
  · left
    rw [Filter.EventuallyEq, eventually_nhds_iff] at h₁f
    obtain ⟨t, ht⟩ := h₁f
    rw [Filter.EventuallyEq, eventually_nhds_iff]
    use t
    constructor
    · intro y hy
      simp [ht.1 y hy]
    · exact ht.2
  · right
    obtain ⟨n, g_f, h₁g_f, h₂g_f, h₃g_f⟩ := h₁f
    use n, g * g_f, h₁g.mul h₁g_f
    constructor
    · simp
      exact ⟨h₂g, h₂g_f⟩
    · rw [Filter.EventuallyEq, eventually_nhds_iff] at h₃g_f
      obtain ⟨t, ht⟩ := h₃g_f
      rw [Filter.EventuallyEq, eventually_nhds_iff]
      use t
      constructor
      · intro y hy
        simp
        rw [ht.1]
        simp
        ring
        exact hy
      · exact ht.2

/- A function is strongly meromorphic at a point iff it is strongly meromorphic
   after multiplication with a non-vanishing analytic function
-/
theorem MeromorphicNFAt_of_mul_analytic
  {f g : 𝕜 → 𝕜}
  {z₀ : 𝕜}
  (h₁g : AnalyticAt 𝕜 g z₀)
  (h₂g : g z₀ ≠ 0) :
  MeromorphicNFAt f z₀ ↔ MeromorphicNFAt (f * g) z₀ := by
  constructor
  · apply MeromorphicNFAt_of_mul_analytic' h₁g h₂g
  · intro hprod
    have : f =ᶠ[𝓝 z₀] f * g * g⁻¹ := by
      filter_upwards [h₁g.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr h₂g)]
      intro y hy
      rw [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_singleton_iff] at hy
      simp [hy]
    rw [meromorphicNFAt_congr this]
    exact MeromorphicNFAt_of_mul_analytic' (h₁g.inv h₂g) (inv_ne_zero h₂g) (f := f * g) hprod

theorem MeromorphicNFAt.order_eq_zero_iff {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicNFAt f x) :
    hf.meromorphicAt.order = 0 ↔ f x ≠ 0 := by
  constructor
  · intro h₁f
    have h₂f := hf.analyticAt (le_of_eq h₁f.symm)
    apply h₂f.order_eq_zero_iff.1
    apply WithTopCoe
    simp_all only [h₂f.meromorphicAt_order]
    exact h₁f
  · intro h
    have hf' := hf
    rcases hf with h₁ | h₁
    · have := h₁.eq_of_nhds
      tauto
    · obtain ⟨n, g, h₁g, h₂g, h₃g⟩ := h₁
      have : n = 0 := by
        by_contra hContra
        have := Filter.EventuallyEq.eq_of_nhds h₃g
        simp [zero_zpow n hContra] at this
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
    · apply eventuallyEq_nhdsWithin_of_eventuallyEq_nhds h
      let h₁f := cs
      rw [hf.order_eq_zero_iff] at h₁f
      let h₁g := cs
      rw [t₀, hg.order_eq_zero_iff] at h₁g
      simp_all
  · exact (Filter.EventuallyEq.filter_mono · nhdsWithin_le_nhds)


theorem MeromorphicNFAt.eliminate
  {f : 𝕜 → 𝕜}
  {z₀ : 𝕜}
  (h₁f : MeromorphicNFAt f z₀)
  (h₂f : h₁f.meromorphicAt.order ≠ ⊤) :
  ∃ g : 𝕜 → 𝕜, (AnalyticAt 𝕜 g z₀)
    ∧ (g z₀ ≠ 0)
    ∧ (f = (fun z ↦ (z-z₀) ^ (h₁f.meromorphicAt.order.untop h₂f)) * g) := by

  let g₁ := (fun z ↦ (z-z₀) ^ (-h₁f.meromorphicAt.order.untop h₂f)) * f
  let g₁₁ := fun z ↦ (z-z₀) ^ (-h₁f.meromorphicAt.order.untop h₂f)
  have h₁g₁₁ : MeromorphicAt g₁₁ z₀ := by fun_prop
  have h₂g₁₁ : h₁g₁₁.order = - h₁f.meromorphicAt.order.untop h₂f := by
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
    rw [h₁g₁₁.order_eq_int_iff]
    use 1
    constructor
    · exact analyticAt_const
    · constructor
      · simp
      · apply eventually_nhdsWithin_of_forall
        simp [g₁₁]
  have h₁g₁ : MeromorphicAt g₁ z₀ := h₁g₁₁.mul h₁f.meromorphicAt
  have h₂g₁ : h₁g₁.order = 0 := by
    rw [h₁g₁₁.order_mul h₁f.meromorphicAt, h₂g₁₁]
    simp only [WithTop.coe_untop, g₁₁]
    rw [add_comm, LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top h₂f]
  let g := h₁g₁.toNF
  use g
  have h₁g : MeromorphicNFAt g z₀ := by
    exact MeromorphicAt.MeromorphicNFAt_of_toNF h₁g₁
  have h₂g : h₁g.meromorphicAt.order = 0 := by
    rw [← h₁g₁.order_congr h₁g₁.toNF_id_on_punct_nhd]
    exact h₂g₁
  constructor
  · apply analyticAt
    · rw [h₂g]
    · exact h₁g
  · constructor
    · rwa [← h₁g.order_eq_zero_iff]
    · funext z
      by_cases hz : z = z₀
      · by_cases hOrd : h₁f.meromorphicAt.order.untop h₂f = 0
        · simp [hOrd]
          have : MeromorphicNFAt g₁ z₀ := by
            unfold g₁
            simp [hOrd]
            have : (fun z => 1) * f = f := by
              funext z
              simp
            rwa [this]
          rw [hz]
          unfold g
          rw [← toNF_eq_id this]
          unfold g₁
          rw [hOrd]
          simp
        · have : h₁f.meromorphicAt.order ≠ 0 := by
            by_contra hC
            simp_rw [hC] at hOrd
            tauto
          let A := h₁f.order_eq_zero_iff.not.1 this
          simp at A
          rw [hz, A]
          simp
          left
          rwa [zpow_eq_zero_iff]
      · simp
        have : g z = g₁ z := (h₁g₁.toNF_id_on_complement hz).symm
        rw [this]
        unfold g₁
        simp [hz]
        rw [← mul_assoc, mul_inv_cancel₀]
        simp
        apply zpow_ne_zero
        exact sub_ne_zero_of_ne hz
