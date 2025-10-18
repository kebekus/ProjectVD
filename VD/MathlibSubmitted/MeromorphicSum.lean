import Mathlib.Analysis.Meromorphic.Basic

open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem MeromorphicAt.sum {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    MeromorphicAt (∑ n ∈ s, f n) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    exact analyticAt_const.meromorphicAt
  | insert σ s hσ hind =>
    rw [Finset.sum_insert hσ]
    exact (h σ).add hind

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem MeromorphicAt.fun_sum {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    MeromorphicAt (fun z ↦ ∑ n ∈ s, f n z) x := by
  convert sum h (s := s)
  simp

/-- Finite sums of meromorphic functions are meromorphic. -/
lemma MeromorphicOn.sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E}
    (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (∑ n ∈ s, f n) U :=
  fun z hz ↦ MeromorphicAt.sum (fun σ ↦ h σ z hz)

/-- Finite sums of meromorphic functions are meromorphic. -/
lemma MeromorphicOn.fun_sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E}
    (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (fun z ↦ ∑ n ∈ s, f n z) U :=
  fun z hz ↦ MeromorphicAt.fun_sum (fun σ ↦ h σ z hz)
