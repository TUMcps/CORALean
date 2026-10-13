import CORALean.ContDynamics.NonlinearSys.Definitions.FloatModel
import CORALean.ContSet.Interval.Float.Operations.CentreMat
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# `linearizeFloat`, the matrices a float step linearizes with

CORA's `linearize` in `𝕋`: `A` and `B` are the Jacobian blocks at the expansion
point `(x✱, u✱)`, here the centres of the model's enclosures of them at that point.

Any pair would do. `AbstractionError` does not ask `A` and `B` to be the
derivative, and the remainder `slopeRemainder` encloses is taken against whatever
pair this returns, so a centre rounded either way costs a slightly larger
remainder and nothing else. That is why no real counterpart has to be named:
`NonlinearSys.linearize` reads off whatever matrix it is given.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(A, B)`: the centres of the model's `∂f/∂x` and `∂f/∂u` at `(xs, us)`. -/
def NonlinearSys.FloatModel.linearizeFloat (fm : NonlinearSys.FloatModel 𝕋 n m) (xs : Vec 𝕋 n)
    (us : Vec 𝕋 m) : Mat 𝕋 n n × Mat 𝕋 n m :=
  let Jx := fm.jacX (Interval.point xs) (Interval.point us)         -- [∂f/∂x (x✱, u✱)]
  let Ju := fm.jacU (Interval.point xs) (Interval.point us)         -- [∂f/∂u (x✱, u✱)]
  (Jx.centreMat, Ju.centreMat)                                      -- A, B

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
