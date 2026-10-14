module

public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachStep

@[expose] public section

/-!
# `Alg. 3` lines 6-13: the loop

`maxBackReachRun`: [1, Alg. 3] lines 6-13, the state after the first `k` iterations; `0` is
line 2's pre-loop state, so the `k`-th iteration's set is `run (k+1)`'s.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 6-13: the state after the first `k` iterations; `0` is line 2's
pre-loop state, so the `k`-th iteration's set is `run (k+1)`'s. -/
noncomputable def LinearSys.maxBackReachRun (sys : LinearSys 𝕋 n)
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P₁ P₂ : HPolytope (Vec ℝ n)) (U W₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (t₀ Δt : ℝ) (η : ℕ) : ℕ → LinearSys.MaxBackReachState n
  | 0 => sys.maxBackReachInit U W₀ t₀ η
  | k + 1 => sys.maxBackReachStep ρ P₁ P₂ U W₀ Zw Δt η
      (sys.maxBackReachRun ρ P₁ P₂ U W₀ Zw t₀ Δt η k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
