import VD.ToMathlib.Nevanlinna_mul

open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

/-- Sums of circle integrable functions are circle integrable. -/
theorem CircleIntegrable.fun_sum {c : ℂ} {R : ℝ} {ι : Type*} (s : Finset ι) {f : ι → ℂ → E}
    (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    CircleIntegrable (fun z ↦ ∑ i ∈ s, f i z) c R := by
  convert CircleIntegrable.sum s h
  simp

variable [ProperSpace E]

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem MeromorphicAt.sum {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜} {x : 𝕜}
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
theorem MeromorphicAt.fun_sum {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    MeromorphicAt (fun z ↦ ∑ n ∈ s, f n z) x := by
  convert sum h (s := s)
  simp

/-- Finite sums of meromorphic functions are meromorphic. -/
lemma MeromorphicOn.sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (∑ n ∈ s, f n) U :=
  fun z hz ↦ MeromorphicAt.sum (fun σ ↦ h σ z hz)

/-- Finite sums of meromorphic functions are meromorphic. -/
lemma MeromorphicOn.fun_sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (fun z ↦ ∑ n ∈ s, f n z) U :=
  fun z hz ↦ MeromorphicAt.fun_sum (fun σ ↦ h σ z hz)

/--
Variant of `posLog_sum` for norms of elements in normed additive commutative
groups, using monotonicity of `log⁺` and the triangle inequality.
-/
lemma posLog_norm_sum_le {E : Type*} [NormedAddCommGroup E]
    {α : Type*} (s : Finset α) (f : α → E) :
    log⁺ ‖∑ t ∈ s, f t‖ ≤ log s.card + ∑ t ∈ s, log⁺ ‖f t‖ := by
  calc log⁺ ‖∑ t ∈ s, f t‖
  _ ≤ log⁺ (∑ t ∈ s, ‖f t‖) := by
    apply monotoneOn_posLog (by simp) _ (norm_sum_le s f)
    simp [Finset.sum_nonneg (fun  i hi ↦ norm_nonneg (f i))]
  _ ≤ log s.card + ∑ t ∈ s, log⁺ ‖f t‖ :=
    posLog_sum s fun t ↦ ‖f t‖

/-- Circle averages commute with addition. -/
theorem circleAverage_add_fun {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℂ} (hf₁ : CircleIntegrable f₁ c R)
    (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (fun z ↦ f₁ z + f₂ z) c R = circleAverage f₁ c R + circleAverage f₂ c R :=
  circleAverage_add hf₁ hf₂

namespace Function.locallyFinsuppWithin

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*} [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]

end Function.locallyFinsuppWithin

namespace ValueDistribution

variable [ProperSpace 𝕜]

/--
The proximity function of `f + g` at `⊤` is less than or equal to the sum of the
proximity functions of `f` and `g`, plus `log 2`.
-/
theorem proximity_top_add_le {f₁ f₂ : ℂ → ℂ} (h₁f₁ : MeromorphicOn f₁ Set.univ)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) :
    proximity (f₁ + f₂) ⊤ ≤ (proximity f₁ ⊤) + (proximity f₂ ⊤) + (fun _ ↦ log 2) := by
  simp only [proximity, reduceDIte, Pi.add_apply]
  intro r
  have h₂f₁ : MeromorphicOn f₁ (sphere 0 |r|) := fun x _ ↦ h₁f₁ x trivial
  have h₂f₂ : MeromorphicOn f₂ (sphere 0 |r|) := fun x _ ↦ h₁f₂ x trivial
  have h₃f₁ := circleIntegrable_posLog_norm_meromorphicOn h₂f₁
  have h₃f₂ := circleIntegrable_posLog_norm_meromorphicOn h₂f₂
  calc circleAverage (fun x ↦ log⁺ ‖f₁ x + f₂ x‖) 0 r
  _ ≤ circleAverage (fun x ↦ log⁺ ‖f₁ x‖ + log⁺ ‖f₂ x‖ + log 2) 0 r :=
    circleAverage_mono (circleIntegrable_posLog_norm_meromorphicOn (fun_add h₂f₁ h₂f₂))
      ((h₃f₁.add h₃f₂).add (circleIntegrable_const (log 2) 0 r))
      fun x _ ↦ posLog_norm_add_le (f₁ x) (f₂ x)
  _ = circleAverage (log⁺ ‖f₁ ·‖) 0 r + circleAverage (log⁺ ‖f₂ ·‖) 0 r + log 2 := by
    rw [← circleAverage_add h₃f₁ h₃f₂, ← circleAverage_const (log 2),
      ← circleAverage_add (h₃f₁.add h₃f₂) (circleIntegrable_const (log 2) 0 r)]
    congr 1
    ext
    simp [circleAverage_const]

theorem proximity_top_sum_le {α : Type*} (s : Finset α) (f : α → ℂ → ℂ)
    (hf : ∀ a, MeromorphicOn (f a) Set.univ) :
    proximity (∑ a ∈ s, f a) ⊤ ≤ ∑ a ∈ s, (proximity (f a) ⊤) + (fun _ ↦ log s.card):= by
  simp only [proximity, reduceDIte, Finset.sum_apply]
  intro r
  simp only [Pi.add_apply, Finset.sum_apply]
  calc circleAverage (fun x ↦ log⁺ ‖∑ c ∈ s, f c x‖) 0 r
  _ ≤ circleAverage (fun x ↦ ∑ c ∈ s, log⁺ ‖f c x‖ + log s.card) 0 r := by
    apply circleAverage_mono
    · apply circleIntegrable_posLog_norm_meromorphicOn
      apply MeromorphicOn.mono_set (MeromorphicOn.fun_sum (hf ·)) (by tauto)
    · apply CircleIntegrable.add _ (circleIntegrable_const (log s.card) 0 r)
      apply CircleIntegrable.fun_sum
      intro i hi
      exact circleIntegrable_posLog_norm_meromorphicOn (fun x _ ↦ hf i x trivial)
    · intro x hx
      rw [add_comm]
      apply posLog_norm_sum_le
  _ = ∑ c ∈ s, circleAverage (fun x ↦ log⁺ ‖f c x‖) 0 r + log s.card := by
    sorry

end ValueDistribution
