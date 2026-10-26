module

public import CORALean.ContDynamics.LinearSys.Theorems.MaxBackReachRunFloatEncloses

@[expose] public section

/-!
# The float run of `Alg. 3` is inside the exact run

The inner approximation, `⊆`, and never `⊇`: the float `R̂^{∃∀}(-τ_{k-1})` after `k` iterations,
the sum of the first summand and the negated second, is inside the exact layer's set of the same
iteration. Whatever `maxBackReachTimeInterval_inner` says of the exact run's sets, it says of the
float's, which are inside them. This is the `R` of `maxBackReachRunFloat_encloses`.
The lines are those of [1, Alg. 3].

## Inputs
* `sys` – linear system
* `Bx` – conversion box
* `P₁` – first eroded float polytope
* `P₂` – second eroded float polytope
* `U` – input float zonotope
* `W₀` – initial disturbance float zonotope
* `Zw` – center trajectory contribution over a bracket
* `t₀` – float start time
* `Δt` – float step length
* `η` – Taylor order
* `ρ` – support oracle for bounded exact polytopes
* `P₁r` – first exact polytope
* `P₂r` – second exact polytope
* `Ur` – exact input zonotope
* `W₀r` – exact initial disturbance zonotope
* `Zwr` – exact center trajectory contribution
* `k` – iteration count

## Hypotheses
* `ht₀` – start time nonnegative
* `hΔt` – step length positive
* `hU0` – input error box contains zero
* `hU` – exact input zonotope inside the float one
* `hWE` – disturbance error box is zero
* `hW₀r` – exact disturbance zonotope inside the float one
* `hZw` – float center contribution holds the exact one
* `hP₁` – first float polytope inside the exact one
* `hP₂` – second float polytope inside the exact one
* `hP₁0` – first polytope error box contains zero
* `hP₂0` – second polytope error box contains zero
* `hker₁` – first float polytope has no equality rows
* `hker₂` – second float polytope has no equality rows
* `hkerr₁` – first exact polytope has no equality rows
* `hkerr₂` – second exact polytope has no equality rows
* `hP₁b` – the inequality rows of the first exact polytope bound it
* `hP₂b` – the inequality rows of the second exact polytope bound it

## Conclusion
* the float run's sets lie inside the exact run's
## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.maxBackReachRunFloat_inner (sys : LinearSys 𝕋 n) (Bx : Interval (Vec 𝕋 n))
    (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) {U W₀ : Zonotope (Vec 𝕋 n)} {Zw : 𝕋 → 𝕋 → Zonotope (Vec 𝕋 n)}
    {t₀ Δt : 𝕋} {η : ℕ}
    (ρ : ∀ (P : CORALean.Real.HPolytope (Vec ℝ n)) (_ : Bornology.IsBounded P.construct)
      (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P₁r P₂r : CORALean.Real.HPolytope (Vec ℝ n))
    (Ur W₀r : CORALean.Real.Zonotope (Vec ℝ n)) (Zwr : ℝ → CORALean.Real.Zonotope (Vec ℝ n))
    (ht₀ : 0 ≤ toReal t₀) (hΔt : 0 < toReal Δt) (hU0 : (0 : Vec ℝ n) ∈ U.I_error.construct)
    (hU : U.construct ⊆ construct Ur) (hWE : W₀.I_error = Interval.point fun _ => FloatOps.zero)
    (hW₀r : W₀r.construct ⊆ W₀.construct)
    (hZw : ∀ (tLo tHi : 𝕋) (t : ℝ), toReal tLo ≤ t → t ≤ toReal tHi →
      construct (Zwr t) ⊆ (Zw tLo tHi).construct) (hP₁ : P₁.construct ⊆ P₁r.construct)
    (hP₂ : P₂.construct ⊆ P₂r.construct) (hP₁0 : (0 : Vec ℝ n) ∈ P₁.I_error.construct)
    (hP₂0 : (0 : Vec ℝ n) ∈ P₂.I_error.construct)
    (hker₁ : ∀ i (y : Vec ℝ n), (toRealMat P₁.Ae *ᵥ y) i = 0)
    (hker₂ : ∀ i (y : Vec ℝ n), (toRealMat P₂.Ae *ᵥ y) i = 0)
    (hkerr₁ : ∀ (i : Fin P₁r.me) (y : Vec ℝ n), P₁r.Ae i y = 0)
    (hkerr₂ : ∀ (i : Fin P₂r.me) (y : Vec ℝ n), P₂r.Ae i y = 0)
    (hP₁b : Bornology.IsBounded P₁r.dropEqs.construct)
    (hP₂b : Bornology.IsBounded P₂r.dropEqs.construct) (k : ℕ) : -- --- CONCL ---
    ∀ s ∈ sys.maxBackReachRunFloat Bx P₁ P₂ U W₀ Zw t₀ Δt η k,
      ∃ ηr, sys.reachOrderFloat t₀ t₀ η = some ηr ∧ sys.reachOrderFloat Δt Δt η = some ηr ∧
        s.R ⊆ construct
          (sys.maxBackReachRun ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr (toReal t₀) (toReal Δt) ηr
            k).R := by -- --- PROOF ---
  intro s (h : sys.maxBackReachRunFloat Bx P₁ P₂ U W₀ Zw t₀ Δt η k = some s)
  obtain ⟨ηr, h₀, h₁, henc⟩ := sys.maxBackReachRunFloat_encloses Bx P₁ P₂ ρ P₁r P₂r Ur W₀r Zwr
    ht₀ hΔt hU0 hU hWE hW₀r hZw hP₁ hP₂ hP₁0 hP₂0 hker₁ hker₂ hkerr₁ hkerr₂ hP₁b hP₂b k _ h
  exact ⟨ηr, h₀, h₁, henc.R⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
