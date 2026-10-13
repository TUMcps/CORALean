module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CurvatureEnclosure
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.GenMinus
public import CORALean.Global.Err
public import CORALean.Global.EuclideanGenOpNorm

@[expose] public section

/-!
# `Δε^h_k`, eq. (23)

`affineDynamicsError`: `Δε^h_k(Δt,η) := 2·err(C) + √γ_h ‖G^{(-)}_h‖₂`, the error [1, Prop. 1]
charges the affine dynamics for one step.

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

/-- [1]'s eq. (23): `Δε^h_k(Δt,η) := 2·err(C) + √γ_h ‖G^{(-)}_h‖₂`. -/
noncomputable def MatExp.affineDynamicsError (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) (η : ℕ) : ℝ :=
  2 * err (MatExp.curvatureEnclosure A H ũ Δt η).construct
    + Real.sqrt H.h * genOpNorm₂ (MatExp.genMinus A H Δt)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
