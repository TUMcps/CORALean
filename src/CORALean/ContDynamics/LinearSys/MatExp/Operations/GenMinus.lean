module

public import CORALean.ContSet.Zonotope.Real.Instances
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# `G^{(-)}_h`, eq. (23)

`genMinus`: [1]'s eq. (23) `G^{(-)}_h = (e^{AΔt} - I_n)G_h`, one column per generator.

## Inputs
* `A` – system matrix
* `H` – state zonotope
* `Δt` – step length

## Output
* generator columns of the propagated minus the initial zonotope

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
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

/-- [1]'s eq. (23) `G^{(-)}_h = (e^{AΔt} - I_n)G_h`, one column per generator. -/
noncomputable def MatExp.genMinus (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n)) (Δt : ℝ) :
    Fin H.h → Vec ℝ n :=
  fun l => (exp (Δt • A) - 1).mulVec (H.G l)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
