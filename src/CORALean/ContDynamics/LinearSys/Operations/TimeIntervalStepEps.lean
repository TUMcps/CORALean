module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderOrder
public import CORALean.ContDynamics.LinearSys.Operations.TimeInterval

@[expose] public section

/-!
# A step stated against an admissible error rather than an order

`timeInterval` with its truncation order chosen instead of given: the caller says how much
remainder it will tolerate and `expRemainderOrder` names the least order meeting it. What that
buys is in `timeIntervalStepEps_outer`: the side condition `‖rA‖/(η+2) < 1` a caller of
`timeInterval` has to discharge is discharged by the selector, so `0 < ε` is all that is left.
**`ε` is one term of the enclosure's error and not all of it.** [1] tunes the step too.
`timeInterval_subset_reach_add_error` measures how far `construct` of the result exceeds what
the flow visits, and `ε` reaches only the second-order part of that: over a whole step the convex
hull costs a first-order excess no order touches.

## Inputs
* `sys` – linear system
* `r` – step length
* `ε` – admissible error
* `X₀` – initial set

## Output
* time-interval step at the least order whose remainder stays under the error

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

/-- `timeInterval` at the least order whose exponential remainder stays
under `ε`. -/
noncomputable def LinearSys.timeIntervalStepEps
    (sys : LinearSys 𝕋 n) (r ε : ℝ) (X₀ : S n) : S n :=
  sys.timeInterval r (MatExp.expRemainderOrder (r • toRealMat sys.A) ε) X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
