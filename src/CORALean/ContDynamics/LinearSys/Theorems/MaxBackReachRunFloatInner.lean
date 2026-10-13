module

public import CORALean.ContDynamics.LinearSys.Theorems.MaxBackReachRunFloatEncloses

@[expose] public section

/-!
# The float run of `Alg. 2` is inside the exact run

The inner approximation, `⊆`, and never `⊇`: the float `R̂^{∃∀}(-τ_{k-1})` after `k` iterations,
the sum of the first summand and the negated second, is inside the exact layer's set of the same
iteration. Whatever `maxBackReachTimeInterval_inner` says of the exact run's sets, it says of the
float's, which are inside them. This is the `R` of `maxBackReachRunFloat_encloses`.
The lines are those of [1, Alg. 2].

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.maxBackReachRunFloat_inner (sys : LinearSys 𝕋 n) (Bx : Interval (Vec 𝕋 n))
    (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) {U W₀ : Zonotope (Vec 𝕋 n)}
    {Zw : 𝕋 → 𝕋 → Zonotope (Vec 𝕋 n)} {t₀ Δt : 𝕋}
    {η : ℕ}
    (ρ : ∀ (P : CORALean.Real.HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ),
      SupportBound P.construct c)
    (P₁r P₂r : CORALean.Real.HPolytope (Vec ℝ n)) (Ur W₀r : CORALean.Real.Zonotope (Vec ℝ n))
    (Zwr : ℝ → CORALean.Real.Zonotope (Vec ℝ n)) (ht₀ : 0 ≤ toReal t₀) (hΔt : 0 < toReal Δt)
    (hU0 : (0 : Vec ℝ n) ∈ U.E.construct) (hU : U.construct ⊆ construct Ur)
    (hWE : W₀.E = Interval.point fun _ => FloatOps.zero) (hW₀r : W₀r.construct ⊆ W₀.construct)
    (hZw : ∀ (tLo tHi : 𝕋) (t : ℝ), toReal tLo ≤ t → t ≤ toReal tHi →
      construct (Zwr t) ⊆ (Zw tLo tHi).construct)
    (hP₁ : P₁.construct ⊆ P₁r.construct) (hP₂ : P₂.construct ⊆ P₂r.construct)
    (hker₁ : ∀ i (y : Vec ℝ n), (toRealMat P₁.Ae *ᵥ y) i = 0)
    (hker₂ : ∀ i (y : Vec ℝ n), (toRealMat P₂.Ae *ᵥ y) i = 0)
    (hkerr₁ : ∀ (i : Fin P₁r.me) (y : Vec ℝ n), P₁r.Ae i y = 0)
    (hkerr₂ : ∀ (i : Fin P₂r.me) (y : Vec ℝ n), P₂r.Ae i y = 0) (k : ℕ)
    {s : LinearSys.MaxBackReachStateFloat 𝕋 n}
    (h : sys.maxBackReachRunFloat Bx P₁ P₂ U W₀ Zw t₀ Δt η k = some s) :
    ∃ ηr, sys.reachOrderFloat t₀ t₀ η = some ηr ∧ sys.reachOrderFloat Δt Δt η = some ηr ∧
      s.R ⊆ construct
        (sys.maxBackReachRun ρ P₁r P₂r Ur W₀r Zwr (toReal t₀) (toReal Δt) ηr
          k).R := by
  obtain ⟨ηr, h₀, h₁, henc⟩ := sys.maxBackReachRunFloat_encloses Bx P₁ P₂ ρ P₁r P₂r Ur W₀r Zwr
    ht₀ hΔt hU0 hU hWE hW₀r hZw hP₁ hP₂ hker₁ hker₂ hkerr₁ hkerr₂ k h
  exact ⟨ηr, h₀, h₁, henc.R⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
