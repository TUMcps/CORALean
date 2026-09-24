import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderOrder
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep

/-!
# A step stated against an admissible error rather than an order

`timeIntervalStep` with its truncation order chosen instead of given: the
caller says how much remainder it will tolerate and `expRemainderOrder` names
the least order meeting it. What that buys is in `timeIntervalStepEps_outer` —
the side condition `‖rA‖/(η+2) < 1` a caller of `timeIntervalStep` has to
discharge is discharged by the selector, so `0 < ε` is all that is left.

**`ε` is one term of the enclosure's error and not all of it.**
`timeIntervalStep_subset_reach_add_error` measures how far `construct` of the
result exceeds what the flow visits, and `ε` reaches only the second-order part
of that: over a whole step the convex hull costs a first-order excess no order
touches. Adaptive reachability in the sense of [1] tunes the step size and the
zonotope order as well; this is one knob of that, chosen soundly.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `timeIntervalStep` at the least order whose exponential remainder stays
under `ε`. -/
noncomputable def LinearSys.timeIntervalStepEps
    (sys : LinearSys 𝕋 n) (r ε : ℝ) (X₀ : S n) : S n :=
  sys.timeIntervalStep r (MatExp.expRemainderOrder (r • toRealMat sys.A) ε) X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
