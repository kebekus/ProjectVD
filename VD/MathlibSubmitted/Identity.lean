import Mathlib.Analysis.Complex.OpenMapping

open Complex Real

/--
Corollary to the open mapping theorem: A holomorphic function whose real part is
constant is itself constant.
-/
theorem AnalyticOnNhd.constant_if_re_constant {f : ℂ → ℂ} {U : Set ℂ} {c₀ : ℝ}
    (h₁f : AnalyticOnNhd ℂ f U) (h₂f : ∀ x ∈ U, (f x).re = c₀) (h₁U : IsOpen U) (h₂U : IsConnected U) :
    ∃ c, ∀ x ∈ U, f x = c := by
  obtain ⟨z₀, _⟩ := h₂U.nonempty
  by_contra h₅
  grind [not_isOpen_singleton (c₀ : ℝ), (by aesop : (re '' (f '' U)) = { c₀ }), isOpenMap_re (f '' U)
    ((h₁f.is_constant_or_isOpen h₂U.isPreconnected).resolve_left h₅ U (by tauto) h₁U)]

/--
Corollary to the open mapping theorem: A holomorphic function whose real part is
constant is itself constant.
-/
theorem AnalyticOnNhd.constant_if_re_constant₁ {f : ℂ → ℂ} {U : Set ℂ} {c₀ : ℝ}
    (h₁f : AnalyticOnNhd ℂ f U) (h₂f : ∀ x ∈ U, (f x).re = c₀) (h₁U : IsOpen U) (h₂U : IsConnected U) :
    ∃ (c : ℝ), ∀ x ∈ U, f x = c₀ + c * I := by
  obtain ⟨cc, hcc⟩ := constant_if_re_constant h₁f h₂f h₁U h₂U
  use cc.im
  simp_rw [Complex.ext_iff]
  aesop
