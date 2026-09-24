import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuter
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuterCorrelated
import CORALean.Global.Err

/-!
# `Δε^U_k`, eq. (25)

`particularSolutionError`: [1]'s eq. (25): `Δε^U_k(Δt,η)`, the correlated and decorrelated
`err`s added: `err(e^{Atk}((Σᵢ₌₁^η Ãᵢ)U0 ⊕ E(Δt,η)ΔtU0)) + err(e^{Atk}(⊕ᵢ₌₁^η ÃᵢU0 ⊕
E(Δt,η)ΔtU0))`. Both start at `i0 = 1`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


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
