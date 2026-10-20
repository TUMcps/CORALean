module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.Global.Err
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# `particularSolutionError`'s explicit bound

`particularSolutionErrorBound`: [1]'s `Δt`-polynomial `√n` times which dominates
`particularSolutionError` — twice the one bound both its summands share, since both start
their sum at `i0 = 1`. `err`'s own triangle inequality otherwise unused.

## Inputs
* `A` – system matrix
* `tk` – step start time
* `U0` – input set
* `Δt` – step length
* `η` – Taylor order

## Output
* polynomial in the step length bounding the particular solution error

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

/-- The `Δt`-polynomial `√n` times which dominates `particularSolutionError` — twice the one
bound both its summands share, since both start their sum at `i0 = 1`. -/
noncomputable def MatExp.particularSolutionErrorBound (A : Mat ℝ n n) (tk : ℝ)
    (U0 : Set (Vec ℝ n)) (Δt : ℝ) (η : ℕ) : ℝ :=
  2 * (∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂) *
    ((∑ i ∈ Finset.Ico 1 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
        * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0)
      + (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
