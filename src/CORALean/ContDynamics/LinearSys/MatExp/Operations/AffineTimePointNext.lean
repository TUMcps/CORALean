module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.Shift
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# `H(t_{k+1})`

`affineTimePointNext`: [1]'s `H(t_{k+1}) = e^{AΔt}H(t_k) ⊕ A^{-1}(e^{AΔt}-I_n)ũ`, Lines 6-7 of
[1, Alg. 1], with `A^{-1}(e^{AΔt}-I_n)ũ` taken as `MatExp.expIntegral`, the power series [1]
itself falls back on when `A` is singular.

## Inputs
* `A` – system matrix
* `H` – state zonotope
* `ũ` – constant input
* `Δt` – step length

## Output
* zonotope of the affine dynamics at the next time point

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
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

/-- [1]'s `H(t_{k+1}) = e^{AΔt}H(t_k) ⊕ A^{-1}(e^{AΔt}-I_n)ũ`, Lines 6-7 of [1, Alg. 1]. -/
noncomputable def MatExp.affineTimePointNext (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) : Zonotope (Vec ℝ n) :=
  -- 6.-7. H(t_{k+1}) ← e^{AΔt}H(t_k) ⊕ A^{-1}(e^{AΔt} - I_n)ũ
  (Zonotope.mtimes (exp (Δt • A)) H).shift (-(MatExp.expIntegral A Δt).mulVec ũ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
