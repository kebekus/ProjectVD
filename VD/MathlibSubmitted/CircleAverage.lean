import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic

open Complex Filter Function MeromorphicOn Metric Real Set Classical Topology --ValueDistribution

/-!
## Additional Material
-/


/-!
## Formula goes here
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {R : ℝ} {x c w : ℂ} {f h : ℂ → ℂ}


open ComplexConjugate Metric Real

variable {R : ℝ} {w z : ℂ}



@[fun_prop]
theorem Real.Continuous.circleAverage {f : ℂ → E}
    (hf : Continuous f) :
    Continuous (Real.circleAverage f c) := by
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  fun_prop

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable,
then `g • f` is circle integrable.
-/
theorem CircleIntegrable.continuousOn_smul
    {E 𝕜 : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    {f : ℂ → E} {g : ℂ → 𝕜} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (g • f) c R :=
  IntervalIntegrable.continuousOn_smul hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable,
then `g • f` is circle integrable.
-/
theorem CircleIntegrable.continuousOn_fun_smul
    {E 𝕜 : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    {f : ℂ → E} {g : ℂ → 𝕜} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (fun z ↦ g z • f z) c R :=
  hf.continuousOn_smul hg

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable,
then `g * f` is circle integrable.
-/
theorem CircleIntegrable.continuousOn_mul
    {𝕜 : Type*} [NormedRing 𝕜]
    {f g : ℂ → 𝕜} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (g * f) c R :=
  IntervalIntegrable.continuousOn_mul hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable,
then `g * f` is circle integrable.
-/
theorem CircleIntegrable.continuousOn_fun_mul
    {𝕜 : Type*} [NormedRing 𝕜]
    {f g : ℂ → 𝕜} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (fun z ↦ g z * f z) c R :=
  hf.continuousOn_mul hg

theorem CircleIntegrable.sub {E : Type*} [NormedAddCommGroup E] {f g : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    CircleIntegrable (f - g) c R :=
  IntervalIntegrable.sub hf hg
