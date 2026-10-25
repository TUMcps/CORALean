module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuterCorrelated
public import CORALean.Global.Err

@[expose] public section

/-!
# `Δε^U_k`, eq. (25)

`particularSolutionError`: [1]'s eq. (25): `Δε^U_k(Δt,η)`, the correlated and decorrelated
`err`s added: `err(e^{Atk}((Σᵢ₌₁^η Ãᵢ)U0 ⊕ E(Δt,η)ΔtU0)) + err(e^{Atk}(⊕ᵢ₌₁^η ÃᵢU0 ⊕
E(Δt,η)ΔtU0))`. Both start at `i0 = 1`.

## Inputs
* `A` – system matrix
* `tk` – step start time
* `U0` – input set
* `Δt` – step length
* `η` – Taylor order

## Output
* sum of the correlated and decorrelated errors

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

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s eq. (25): `Δε^U_k(Δt,η)`, the correlated and decorrelated `err`s added. -/
noncomputable def MatExp.particularSolutionError (A : Mat ℝ n n) (tk : ℝ)
    (U0 : Set (Vec ℝ n)) (Δt : ℝ) (η : ℕ) : ℝ :=
  err ((fun x => (exp (tk • A)).mulVec x) '' MatExp.particularSolutionOuterCorrelated A U0 1 Δt η)
    + err ((fun x => (exp (tk • A)).mulVec x) '' MatExp.particularSolutionOuter A U0 1 Δt η)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
