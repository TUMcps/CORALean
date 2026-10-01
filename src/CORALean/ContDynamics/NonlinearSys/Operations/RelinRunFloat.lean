import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepFloat

/-!
# The float re-linearization loop

`relinStepFloat` iterated `k` times, the set a step reaches at its end being the
set the next one starts from — the while loop of [1, Alg. 1] — collecting each
step's set over its whole interval. One failed step fails the run: a later step
would start from a set nothing has enclosed.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R(τ_0), …, R(τ_{k-1})` of `k` re-linearized steps from `R`, or `none` if
one of them fails. -/
def NonlinearSys.FloatModel.relinRunFloat (fm : NonlinearSys.FloatModel 𝕋 n m)
    (U : Zonotope 𝕋 m) (options : LinearSys.ReachOptions 𝕋) :
    ℕ → Zonotope 𝕋 n → Option (List (Zonotope 𝕋 n))
  | 0, _ => some []
  | k + 1, R => do
    let step ← fm.relinStepFloat U options R                        -- (R(τ), R(t + Δt))
    let rest ← fm.relinRunFloat U options k step.2                  -- the steps after it
    pure (step.1 :: rest)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
