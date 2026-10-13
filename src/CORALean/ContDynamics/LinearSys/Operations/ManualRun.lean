import CORALean.ContDynamics.LinearSys.Operations.ManualInit
import CORALean.ContDynamics.LinearSys.Operations.ManualStep

/-!
# `Alg. 1` lines 4-11: the loop

`manualRun`: [1, Alg. 1] lines 4-11, iterate `manualStep` `k` times, reaching the state at
`t_k`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
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

/-- Lines 4-11: iterate `manualStep` `k` times, reaching the state at `t_k`. -/
noncomputable def LinearSys.manualRun (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec ℝ n))
    (Δt : ℝ) (η ρ : ℕ) : ℕ → LinearSys.ManualState n
  | 0 => LinearSys.manualInit X₀
  | k + 1 => (sys.manualStep X₀ U Δt η ρ (sys.manualRun X₀ U Δt η ρ k)).1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
