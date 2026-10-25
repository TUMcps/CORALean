module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
public import CORALean.ContSet.Interval.Real.Operations.AbsMax
public import CORALean.ContSet.Interval.Real.Operations.OfCenterRadius
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# `MatExp.exponentialRemainder`

CORA's `@intervalMatrix/exponentialRemainder`: with `M = abs(intMat)` (`absMax`), the interval
matrix `[-W, W]` for `W = e^M - Σ_{i ≤ η} Mⁱ/i!`. CORA answers `[-∞, ∞]` when `expm(M)` overflows
to NaN; the exponential of a real matrix is always finite here, so that branch has no counterpart.
It is the quantity of [1, Eq. 6] at the dominating matrix of the box, not the norm bound
`expRemainderBound`.

## Inputs
* `A` – interval matrix
* `η` – Taylor order

## Output
* interval matrix of the exponential remainder

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control, 2012.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `E = intervalMatrix(zeros, W)` with `W = e^M - Σ_{i ≤ η} Mⁱ/i!` at `M = abs(intMat)`. -/
noncomputable def MatExp.exponentialRemainder (A : Interval (Mat ℝ n n)) (η : ℕ) :
    Interval (Mat ℝ n n) :=
  let M := A.absMax
  let W := exp M - MatExp.expTaylor M η
  Interval.ofCenterRadius 0 W

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
