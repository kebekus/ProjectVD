import VD.MathlibPending.Nevanlinna_counting_integral
import VD.MathlibPending.Nevanlinna_add_proximity

open Function MeromorphicOn Metric Real Set Classical ValueDistribution

theorem meromorphicTrailingCoeffAt_add_eq_left_of_lt
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f₁ f₂ : 𝕜 → E} {x : 𝕜} (hf₂ : MeromorphicAt f₂ x)
  (hf₁ : MeromorphicAt f₁ x) -- probably not needed, need to check
  (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ + f₂) x = meromorphicTrailingCoeffAt f₁ x := by

  have H₁ := meromorphicOrderAt_add_eq_left_of_lt hf₂ h

  by_cases h₁₂ : meromorphicOrderAt f₂ x = ⊤
  · sorry

  lift meromorphicOrderAt f₂ x to ℤ using h₁₂ with n₂ hn₂
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm

  lift meromorphicOrderAt f₁ x to ℤ using (by aesop) with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm

  rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁]

  have : ∀ᶠ (z : 𝕜) in nhdsWithin x {x}ᶜ,
      (f₁ + f₂) z = (z - x) ^ n₁ • ( g₁ + (z - x) ^ (n₂ - n₁) • g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with z h₁z h₂z h₃z
    simp [h₁z, h₂z]
    simp at h
    rw [← smul_assoc]
    congr 1
    simp
    rw [← zpow_add₀]
    simp
    rw [sub_ne_zero]
    aesop

  sorry

namespace ValueDistribution


theorem cartan {r : ℝ} {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) :
    characteristic f ⊤ r
      = circleAverage (logCounting f · r) 0 1 - log ‖meromorphicTrailingCoeffAt f 0‖ := by

  have R : ℝ := by sorry
  have hR : R ≠ 0 := by sorry

  have f1 {a : ℂ} :
      logCounting f a R + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖
        = circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R := by
    have : logCounting f a R = logCounting (fun z ↦ f z - a) 0 R := by
      rw [logCounting_coe_eq_logCounting_sub_const_zero]
      rfl
    rw [this]
    have h₁ : MeromorphicOn (fun z ↦ f z - a) ⊤ :=
      h.sub (MeromorphicOn.const a)
    have tmp := logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const h₁ hR
    have : logCounting (f · - a) ⊤ = logCounting f ⊤ := by
      have : (f · - a) = f - fun _ ↦ a := by rfl
      rw [this, logCounting_sub_const]
      exact h
    rw [this] at tmp
    clear this
    simp at tmp
    rw [sub_eq_iff_eq_add] at tmp
    rw [tmp]
    abel

  have f2 :
      circleAverage (fun a ↦ logCounting f a R + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 =
      circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R) 0 1 := by
    apply circleAverage_congr_sphere
    intro a ha
    simp [f1]
  clear f1

  rw [circleAverage_add_fun (c := 0) (R := 1) (f₁ :=  fun a ↦ logCounting f a R)
    (f₂ := fun a ↦ log ‖meromorphicTrailingCoeffAt (fun x ↦ f x - a) 0‖)] at f2

  have : circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (fun x ↦ f x - a) 0‖) 0 1 = 0 := by

    sorry

  sorry


end ValueDistribution
