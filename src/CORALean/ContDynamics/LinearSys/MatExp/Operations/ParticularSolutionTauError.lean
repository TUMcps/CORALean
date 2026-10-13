module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuter
public import CORALean.Global.Err

@[expose] public section

/-!
# `Δε^{U,τ}_k`, eq. (26)

`particularSolutionTauError`: [1]'s eq. (26): `Δε^{U,τ}_k(Δt,η) := err(e^{Atk} bPU(Δt))`: `bPU`
mapped by the (fixed, `Δt`-independent) matrix `e^{Atk}` and read at `err`.

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

/-- [1]'s eq. (26): `Δε^{U,τ}_k(Δt,η) := err(e^{Atk} bPU(Δt))`. -/
noncomputable def MatExp.particularSolutionTauError (A : Mat ℝ n n) (tk : ℝ)
    (U0 : Set (Vec ℝ n)) (Δt : ℝ) (η : ℕ) : ℝ :=
  err ((fun x => (exp (tk • A)).mulVec x) '' MatExp.particularSolutionOuter A U0 0 Δt η)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
