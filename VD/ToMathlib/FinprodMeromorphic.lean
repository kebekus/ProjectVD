import Mathlib.Analysis.Meromorphic.Basic

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Finite products of meromorphic functions are analytic. -/
theorem Finset.meromorphicAt_prod  {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    MeromorphicAt (∏ n ∈ s, f n) x := by
  classical
  apply Finset.induction (motive := fun s ↦ MeromorphicAt (∏ n ∈ s , f n) x)
  · rw [prod_empty]
    exact analyticAt_const.meromorphicAt
  · intro σ s hσ hind
    rw [prod_insert hσ]
    exact (h σ).mul hind

/-- Finite products of meromorphic functions are analytic. -/
theorem Finset.meromorphicAt_fun_prod  {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    MeromorphicAt (fun z ↦ ∏ n ∈ s, f n z) x := by
  convert s.meromorphicAt_prod h
  simp

/-- Finite products of meromorphic functions are analytic. -/
theorem Finset.meromorphicOn_prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (∏ n ∈ s, f n) U :=
  fun z hz ↦ s.meromorphicAt_prod (fun σ ↦ h σ z hz)

/-- Finite products of meromorphic functions are analytic. -/
theorem Finset.meromorphicOn_fun_prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (fun z ↦ ∏ n ∈ s, f n z) U :=
  fun z hz ↦ s.meromorphicAt_fun_prod (fun σ ↦ h σ z hz)
