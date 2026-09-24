import CORALean.ContDynamics.LinearSys.Operations.MinBackReachStep

/-!
# `Alg. 1` lines 7-15: the loop

`minBackReachRun`: [1, Alg. 1] lines 7-15, the state after the `k`-th iteration, holding
`R̂^∃(-τ_k)`.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 7-15: the state after the `k`-th iteration, holding `R̂^∃(-τ_k)`. -/
noncomputable def LinearSys.minBackReachRun (sys : LinearSys 𝕋 n)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (t₀ Δt : ℝ) (η : ℕ) : ℕ → LinearSys.MinBackReachState n
  | 0 => sys.minBackReachStep CZ W₀ U₀ Zw Δt η (sys.minBackReachInit W₀ U₀ t₀ η)
  | k + 1 => sys.minBackReachStep CZ W₀ U₀ Zw Δt η (sys.minBackReachRun CZ W₀ U₀ Zw t₀ Δt η k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
