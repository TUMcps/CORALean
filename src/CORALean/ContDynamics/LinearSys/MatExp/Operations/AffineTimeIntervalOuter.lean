module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AffineTimePointNext
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CurvatureEnclosure
public import CORALean.ContSet.Zonotope.Real.Operations.LinComb

@[expose] public section

/-!
# `Ĥ(τ_k)`

`affineTimeIntervalOuter`: [1]'s eq. (22) `Ĥ(τ_k) = comb(H(t_k),H(t_{k+1})) ⊕ C`, Line 9 of
[1, Alg. 1], with `C` the curvature set `curvatureEnclosure` already spells.

## Inputs
* `A` – system matrix
* `H` – state zonotope
* `ũ` – constant input
* `Δt` – step length
* `η` – Taylor order

## Output
* zonotope enclosing the time-interval solution of the affine dynamics

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s eq. (22) `Ĥ(τ_k) = comb(H(t_k),H(t_{k+1})) ⊕ C`, Line 9 of [1, Alg. 1]. -/
noncomputable def MatExp.affineTimeIntervalOuter (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) (η : ℕ) : Zonotope (Vec ℝ n) :=
  -- 9. Ĥ(τ_k) ← comb(H(t_k), H(t_{k+1})) ⊕ C, eq. (22)
  (H.linComb (MatExp.affineTimePointNext A H ũ Δt)).plus
    (MatExp.curvatureEnclosure A H ũ Δt η)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
