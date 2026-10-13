import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
import CORALean.Global.Err
import Mathlib.Analysis.Matrix.Normed

/-!
# `particularSolutionTauError`'s explicit bound

`particularSolutionTauErrorBound`: [1]'s `Δt`-polynomial `√n` times which dominates
`particularSolutionTauError` — `e^{Atk}`'s own row sums times
`norm₂_le_of_mem_particularSolutionOuter`'s bound on `bPU`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `Δt`-polynomial `√n` times which dominates `particularSolutionTauError`. -/
noncomputable def MatExp.particularSolutionTauErrorBound (A : Mat ℝ n n) (tk : ℝ)
    (U0 : Set (Vec ℝ n)) (Δt : ℝ) (η : ℕ) : ℝ :=
  (∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂) *
    ((∑ i ∈ Finset.range (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
        * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0)
      + (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
