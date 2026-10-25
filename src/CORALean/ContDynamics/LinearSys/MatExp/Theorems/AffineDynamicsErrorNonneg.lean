module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AffineDynamicsError
public import CORALean.Global.Err
public import CORALean.Global.EuclideanGenOpNorm

@[expose] public section

/-!
# `affineDynamicsError` is nonnegative

`affineDynamicsError_nonneg`: [1]'s `Δε^h_k`, eq. (23), a sum of two nonnegative terms.

## Inputs
* `A` – system matrix
* `H` – state zonotope
* `ũ` – constant input
* `Δt` – step length
* `η` – Taylor order

## Hypotheses
* none

## Conclusion
* the affine dynamics error is nonnegative

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.affineDynamicsError_nonneg (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) (η : ℕ) : 0 ≤ MatExp.affineDynamicsError A H ũ Δt η :=
  add_nonneg (mul_nonneg (by norm_num) (err_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (genOpNorm₂_nonneg _))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
