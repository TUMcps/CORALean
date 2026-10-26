module

public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachStep

@[expose] public section

/-!
# `Alg. 3` lines 6-13: the loop

`maxBackReachRun`: [1, Alg. 3] lines 6-13, the state after the first `k` iterations; `0` is
line 2's pre-loop state, so the `k`-th iteration's set is `run (k+1)`'s.

## Inputs
* `sys` – linear system
* `ρ` – support oracle for bounded polytopes
* `P₁` – first eroded polytope
* `P₂` – second eroded polytope
* `U` – input zonotope
* `W₀` – initial disturbance zonotope
* `Zw` – center trajectory contribution
* `t₀` – start time
* `Δt` – step length
* `η` – Taylor order

## Hypotheses
* `hP₁` – the inequality rows of `P₁` bound it
* `hP₂` – the inequality rows of `P₂` bound it

## Output
* loop state after a given number of iterations
## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       19-September-2026
-- Last update:   26-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 6-13: the state after the first `k` iterations; `0` is line 2's
pre-loop state, so the `k`-th iteration's set is `run (k+1)`'s. -/
noncomputable def LinearSys.maxBackReachRun (sys : LinearSys 𝕋 n)
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (_ : Bornology.IsBounded P.construct)
      (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P₁ P₂ : HPolytope (Vec ℝ n)) (hP₁ : Bornology.IsBounded P₁.dropEqs.construct)
    (hP₂ : Bornology.IsBounded P₂.dropEqs.construct) (U W₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (t₀ Δt : ℝ) (η : ℕ) : ℕ → LinearSys.MaxBackReachState n
  | 0 => sys.maxBackReachInit U W₀ t₀ η
  | k + 1 => sys.maxBackReachStep ρ P₁ P₂ hP₁ hP₂ U W₀ Zw Δt η
      (sys.maxBackReachRun ρ P₁ P₂ hP₁ hP₂ U W₀ Zw t₀ Δt η k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
