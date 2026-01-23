import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction

open Filter Metric Real

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
If two functions differ only on a discrete set, then one is meromorphic iff so
is the other.
-/
theorem _root_.meromorphicOn_congr_codiscreteWithin {f g : 𝕜 → E} (h₁ : f =ᶠ[codiscreteWithin U] g)
    (h₂ : IsOpen U) :
    MeromorphicOn f U ↔ MeromorphicOn g U :=
  ⟨(·.congr_codiscreteWithin h₁ h₂), (·.congr_codiscreteWithin h₁.symm h₂)⟩

open MeromorphicOn in
/--
If `f₁` is meromorphic on an open set `U`, if `f₂` agrees with `f₁` on a codiscrete subset of `U`,
then `f₁` and `f₂` induce the same divisors on `U`.
-/
theorem divisor_congr_codiscreteWithin' {f₁ f₂ : 𝕜 → E}
    (h₁ : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) (h₂ : IsOpen U) :
    divisor f₁ U = divisor f₂ U := by
  by_cases hf₁ : MeromorphicOn f₁ U
  · exact divisor_congr_codiscreteWithin hf₁ h₁ h₂
  · simp [divisor, hf₁, (meromorphicOn_congr_codiscreteWithin h₁ h₂).not.1 hf₁]


namespace ValueDistribution

/--
If two functions differ only on a discrete set, then their proximity functions
agree, except perhaps at radius 0.
-/
lemma proximity_congr_codiscreteWithin {f g : ℂ → E} {a : WithTop E} {r : ℝ}
    (hfg : f =ᶠ[codiscreteWithin (sphere 0 |r|)] g) (hr : r ≠ 0) :
    proximity f a r = proximity g a r := by
  by_cases h : a = ⊤
  all_goals
    simp only [proximity, h, ↓reduceDIte]
    apply circleAverage_congr_codiscreteWithin _ hr
    filter_upwards [hfg] using by aesop

/--
If two functions differ only on a discrete set, then their proximity functions
agree, except perhaps at radius 0.
-/
lemma proximity_congr_codiscrete {f g : ℂ → E} {a : WithTop E} {r : ℝ}
    (hfg : f =ᶠ[codiscrete ℂ] g) (hr : r ≠ 0) :
    proximity f a r = proximity g a r :=
  proximity_congr_codiscreteWithin (hfg.filter_mono (codiscreteWithin.mono (by tauto))) hr

@[simp] lemma proximity_const {c : E} {r : ℝ} :
    proximity (fun _ ↦ c) ⊤ r = log⁺ ‖c‖ := by
  simp [proximity, circleAverage_const]

/--
If two functions differ only on a discrete set, then their logarithmic counting
functions agree.
-/
theorem logCounting_congr_codiscrete [NormedSpace ℂ E] {f g : ℂ → E} (hfg : f =ᶠ[codiscrete ℂ] g) :
    logCounting f = logCounting g := by
  ext a : 1
  by_cases h : a = ⊤
  · simp [h, logCounting]
    congr 2
    exact divisor_congr_codiscreteWithin' hfg isOpen_univ
  · simp [h, logCounting]
    congr 2
    apply divisor_congr_codiscreteWithin' _ isOpen_univ
    filter_upwards [hfg] using by simp

/--
If two functions differ only on a discrete set, then their characteristic
functions agree, except perhaps at radius 0.
-/
theorem characteristic_congr_codiscrete [NormedSpace ℂ E] {a : WithTop E} {r : ℝ} {f g : ℂ → E}
    (hfg : f =ᶠ[codiscrete ℂ] g) (hr : r ≠ 0) :
    characteristic f a r = characteristic g a r := by
  simp [characteristic, proximity_congr_codiscrete hfg hr, logCounting_congr_codiscrete hfg]

end ValueDistribution
