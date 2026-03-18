import Mathlib.Analysis.Meromorphic.NormalForm

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[to_fun (attr := fun_prop)]
theorem meromorphicAt_prod' {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (hf : ∀ i ∈ s, MeromorphicAt (f i) x) :
    MeromorphicAt (∏ i ∈ s, f i) x := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.prod_insert ha]
    apply (hf a (Finset.mem_insert_self a s)).mul
      (hs (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

@[to_fun]
theorem meromorphicOn_prod' {ι : Type*} {s : Finset ι} {U : Set 𝕜} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (hf : ∀ i ∈ s, MeromorphicOn (f i) U) :
    MeromorphicOn (∏ i ∈ s, f i) U :=
  fun x hx ↦ meromorphicAt_prod' (hf · · x hx)

@[fun_prop]
theorem meromorphicAt_finprod {x : 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (hf : ∀ i, MeromorphicAt (f i) x) :
    MeromorphicAt (∏ᶠ i, f i) x := by
  by_cases h₂f : Function.HasFiniteMulSupport f
  · simp_rw [finprod_eq_prod f h₂f]
    apply meromorphicAt_prod'
    aesop
  simp_rw [finprod_of_not_hasFiniteMulSupport h₂f]
  apply MeromorphicAt.const

theorem meromorphicOn_finprod {ι : Type*} {U : Set 𝕜} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (hf : ∀ i, MeromorphicOn (f i) U) :
    MeromorphicOn (∏ᶠ i, f i) U :=
  fun x hx ↦ meromorphicAt_finprod (hf · x hx)

@[to_fun (attr := fun_prop)]
theorem meromorphicAt_sum' {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (hf : ∀ i ∈ s, MeromorphicAt (f i) x) :
    MeromorphicAt (∑ i ∈ s, f i) x := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.sum_insert ha]
    apply (hf a (Finset.mem_insert_self a s)).add
      (hs (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

@[to_fun]
theorem meromorphicOn_sum' {ι : Type*} {s : Finset ι} {U : Set 𝕜} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (hf : ∀ i ∈ s, MeromorphicOn (f i) U) :
    MeromorphicOn (∑ i ∈ s, f i) U :=
  fun x hx ↦ meromorphicAt_sum' (hf · · x hx)

@[fun_prop]
theorem meromorphicAt_finsum {x : 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (hf : ∀ i, MeromorphicAt (f i) x) :
    MeromorphicAt (∑ᶠ i, f i) x := by
  by_cases h₂f : Function.HasFiniteSupport f
  · simp_rw [finsum_eq_sum f h₂f]
    apply meromorphicAt_sum'
    aesop
  simp_rw [finsum_of_not_hasFiniteSupport h₂f]
  apply MeromorphicAt.const

theorem meromorphicOn_finsum {ι : Type*} {U : Set 𝕜} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (hf : ∀ i, MeromorphicOn (f i) U) :
    MeromorphicOn (∑ᶠ i, f i) U :=
  fun x hx ↦ meromorphicAt_finsum (hf · x hx)

/--
The order is additive in products of meromorphic functions.
-/
@[to_fun]
theorem meromorphicOrderAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (hf : ∀ i ∈ s, MeromorphicAt (f i) x) :
    meromorphicOrderAt (∏ i ∈ s, f i) x = ∑ i ∈ s, meromorphicOrderAt (f i) x := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty,
      MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
    simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true]
    apply analyticAt_const.meromorphicNFAt
  | insert a s ha hs =>
    simp_all [Finset.sum_insert ha, Finset.prod_insert ha, meromorphicOrderAt_mul
      (hf a (Finset.mem_insert_self a s))
      (meromorphicAt_prod' (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))]

@[to_fun]
theorem MeromorphicOn.divisor_prod
    {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
    {ι : Type*} {s : Finset ι}
    {U : Set 𝕜} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicOn (f i) U)
    (h₂f : ∀ i ∈ s, ∀ z ∈ U, meromorphicOrderAt (f i) z ≠ ⊤) :
    divisor (∏ i ∈ s, f i) U = ∑ i ∈ s, divisor (f i) U := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact divisor_ofNat 1
  | insert a s ha hs =>
    have : ∀ z ∈ U, meromorphicOrderAt (∏ i ∈ s, f i) z ≠ ⊤ := by
      intro z hz
      simpa [meromorphicOrderAt_prod (fun i hi ↦ h₁f i (Finset.mem_insert_of_mem hi) z hz)]
        using fun i hi ↦ h₂f i (Finset.mem_insert_of_mem hi) z hz
    rw [Finset.prod_insert ha, Finset.sum_insert ha, MeromorphicOn.divisor_mul (by aesop)
        (meromorphicOn_prod' (fun i hi ↦ h₁f i (Finset.mem_insert_of_mem hi)))
        (h₂f a (Finset.mem_insert_self a s)) this,
      hs (fun i hi ↦ h₁f i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ h₂f i (Finset.mem_insert_of_mem hi))]

@[to_fun]
theorem meromorphicNFAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFAt (f i) x)
    (h₂f : Set.Subsingleton {σ ∈ s | f σ x = 0}) :
    MeromorphicNFAt (∏ i ∈ s, f i) x := by
  classical
  have h₃f {τ : ι} (h₁τ : τ ∈ s) (h₂τ : τ ∉ {σ ∈ s | f σ x = 0}) :
      AnalyticAt 𝕜 (f τ) x := by
    rw [← (h₁f τ h₁τ).meromorphicOrderAt_nonneg_iff_analyticAt]
    apply ((h₁f τ h₁τ).meromorphicOrderAt_eq_zero_iff.2 _).symm.le
    rw [Finset.mem_filter, not_and] at h₂τ
    exact h₂τ h₁τ
  by_cases h₄f : {σ ∈ s | f σ x = 0} = ∅
  · exact (Finset.analyticAt_prod _ (fun σ hσ ↦ h₃f hσ (by aesop))).meromorphicNFAt
  rw [Finset.filter_eq_empty_iff] at h₄f
  push_neg at h₄f
  obtain ⟨τ, h₁τ, h₂τ⟩ := h₄f
  have {μ : ι} (hμ : μ ∈ s.erase τ) : f μ x ≠ 0 := by
    by_contra
    have : τ = μ :=  h₂f (by aesop) (by aesop)
    aesop
  rw [← Finset.mul_prod_erase _ _ h₁τ, meromorphicNFAt_mul_iff_left]
  · apply h₁f τ h₁τ
  · apply Finset.analyticAt_prod _ (fun μ hμ ↦ h₃f (Finset.mem_of_mem_erase hμ) (by aesop))
  · rw [Finset.prod_apply, Finset.prod_ne_zero_iff]
    aesop

theorem meromorphicNFAt_finprod {x : 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (h₁f : ∀ i, MeromorphicNFAt (f i) x)
    (h₂f : Set.Subsingleton {σ | f σ x = 0}) :
    MeromorphicNFAt (∏ᶠ i, f i) x := by
  by_cases h₃f : Function.HasFiniteMulSupport f
  · simp_rw [finprod_eq_prod f h₃f]
    apply meromorphicNFAt_prod
    · aesop
    · intro a ha b hb
      aesop
  simp_rw [finprod_of_not_hasFiniteMulSupport h₃f]
  apply AnalyticAt.meromorphicNFAt
  apply analyticAt_const

@[to_fun]
theorem meromorphicNFOn_prod {ι : Type*} {s : Finset ι} {U : Set 𝕜} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFOn (f i) U)
    (h₂f : ∀ x ∈ U, Set.Subsingleton {σ ∈ s | f σ x = 0}) :
    MeromorphicNFOn (∏ i ∈ s, f i) U :=
  fun x hx ↦ meromorphicNFAt_prod (h₁f · · hx) (h₂f x hx)

theorem meromorphicNFOn_finprod {ι : Type*} {U : Set 𝕜} {f : ι → 𝕜 → 𝕜}
    [DecidableEq ι] (h₁f : ∀ i, MeromorphicNFOn (f i) U)
    (h₂f : ∀ x ∈ U, Set.Subsingleton {σ | f σ x = 0}) :
  MeromorphicNFOn (∏ᶠ i, f i) U := by
  intro x hx
  apply meromorphicNFAt_finprod (h₁f · hx) (h₂f x hx)

theorem MeromorphicNFAt.zpow {f : 𝕜 → 𝕜} {n : ℤ} {x : 𝕜} (hf : MeromorphicNFAt f x) :
    MeromorphicNFAt (f ^ n) x := by
  by_cases hn : n = 0
  · simp_all only [zpow_zero]
    apply AnalyticAt.meromorphicNFAt
    apply analyticAt_const
  rcases hf with hf | hf
  · left
    filter_upwards [hf] with z hz
    simp_all only [Pi.zero_apply, Pi.pow_apply, zero_zpow n hn]
  · obtain ⟨m, g, h₁g, h₂g, h₃g⟩ := hf
    right
    use n * m, g ^ n, h₁g.zpow h₂g
    constructor
    · rw [Pi.pow_apply]
      exact zpow_ne_zero n h₂g
    · filter_upwards [h₃g] with z hz
      simp [hz, mul_zpow, (zpow_mul' (z - x) n m).symm]

theorem MeromorphicNFOn.zpow {f : 𝕜 → 𝕜} {n : ℤ} {U : Set 𝕜} (hf : MeromorphicNFOn f U) :
    MeromorphicNFOn (f ^ n) U :=
  fun _ hz ↦ (hf hz).zpow
