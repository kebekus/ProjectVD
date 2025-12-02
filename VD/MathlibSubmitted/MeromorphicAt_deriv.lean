import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow

open Topology

@[simp]
theorem eventually_nhdsNE_eventually_nhds_iff_eventually_nhdsNE
    {α : Type*} [TopologicalSpace α] [T1Space α] {a : α} {p : α → Prop} :
    (∀ᶠ y in 𝓝[≠] a, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝[≠] a, p x := by
  nth_rw 2 [← eventually_eventually_nhdsWithin]
  constructor
  · intro h
    filter_upwards [h] with _ hy
    exact eventually_nhdsWithin_of_eventually_nhds hy
  · intro h
    filter_upwards [h, eventually_nhdsWithin_of_forall fun _ a ↦ a] with _ _ _
    simp_all [IsOpen.nhdsWithin_eq]

theorem Filter.EventuallyEq.nhdsNE_deriv
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f f₁ : 𝕜 → F} {x : 𝕜}
    (h : f₁ =ᶠ[𝓝[≠] x] f) :
    deriv f₁ =ᶠ[𝓝[≠] x] deriv f := by
  rw [Filter.EventuallyEq, ← eventually_nhdsNE_eventually_nhds_iff_eventually_nhdsNE] at *
  filter_upwards [h] with y hy
  apply Filter.EventuallyEq.deriv hy

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

@[fun_prop]
theorem AnalyticAt.deriv₁
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {f : 𝕜 → F} {x : 𝕜}
    (h : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (deriv f) x := by
  obtain ⟨r, hr, h⟩ := h.exists_ball_analyticOnNhd
  exact h.deriv x (by simp [hr])

/--
Derivatives of meromorphic functions are meromorphic.
-/
@[fun_prop]
theorem MeromorphicAt.deriv {f : 𝕜 → E} {x : 𝕜} (h : MeromorphicAt f x) :
    MeromorphicAt (deriv f) x := by
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt] at h
  obtain ⟨n, g, h₁g, h₂g⟩ := h
  have : _root_.deriv (fun z ↦ (z - x) ^ n • g z)
      =ᶠ[𝓝[≠] x] fun z ↦ (n * (z - x) ^ (n - 1)) • g z + (z - x) ^ n • _root_.deriv g z := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁g.eventually_analyticAt,
      eventually_nhdsWithin_of_forall fun _ a ↦ a] with z₀ h₁ h₂
    rw [deriv_fun_smul (DifferentiableAt.zpow (by fun_prop) (by simp_all [sub_ne_zero_of_ne h₂])) (by fun_prop),
      add_comm, deriv_comp_sub_const (f := (· ^ n))]
    aesop
  rw [MeromorphicAt.meromorphicAt_congr (Filter.EventuallyEq.nhdsNE_deriv h₂g),
    MeromorphicAt.meromorphicAt_congr this]
  fun_prop

/--
Derivatives of meromorphic functions are meromorphic.
-/
theorem MeromorphicOn.deriv {s : Set 𝕜} {f : 𝕜 → E} (h : MeromorphicOn f s) :
    MeromorphicOn (deriv f) s := fun z hz ↦ (h z hz).deriv
