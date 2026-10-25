module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalMulVecSet
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeffSum

@[expose] public section

/-!
# [1]'s eq. (25)'s correlated summand: `(Σᵢ Ãᵢ)U0 ⊕ E(Δt,η)ΔtU0`

`particularSolutionOuterCorrelated`: [1]'s eq. (25)'s `Δε^U_k` sums TWO outer-approximations
of the same shape: the decorrelated one, `⊕ᵢ ÃᵢU0`, already `particularSolutionOuter`, and
this one's correlated one, `(Σᵢ Ãᵢ)U0` — a single matrix, the sum of the `Ãᵢ` themselves,
applied once.

## Inputs
* `A` – system matrix
* `U0` – input set
* `i0` – start index
* `Δt` – step length
* `η` – Taylor order

## Output
* correlated summand of the particular solution outer approximation

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s eq. (25)'s correlated summand, as a `Set`: `(Σᵢ Ãᵢ)U0 ⊕ E(Δt,η)ΔtU0`. -/
noncomputable def MatExp.particularSolutionOuterCorrelated (A : Mat ℝ n n)
    (U0 : Set (Vec ℝ n)) (i0 : ℕ) (Δt : ℝ) (η : ℕ) : Set (Vec ℝ n) :=
  (fun x => (MatExp.particularCoeffSum A Δt i0 η).mulVec x) '' U0 +
    MatExp.intervalMulVecSet (MatExp.expRemainderMat A Δt η) (Δt • U0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
