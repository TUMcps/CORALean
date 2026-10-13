import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepAtFloat

/-!
# The float re-linearization loop, at given points

`relinStepAtFloat` iterated `k` times, the set a step reaches at its end being the
set the next one starts from — the while loop of [1, Alg. 1] — collecting each
step's set over its whole interval. One failed step fails the run: a later step
would start from a set nothing has enclosed.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R(τ_0), …, R(τ_{k-1})` of `k` re-linearized steps from `R`, each linearized at the
expansion point `pt` names for its start set, or `none` if one of them fails. -/
def NonlinearSys.FloatModel.relinRunAtFloat (fm : NonlinearSys.FloatModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachOptions 𝕋)
    (pt : Zonotope (Vec 𝕋 n) → Vec 𝕋 n) :
    ℕ → Zonotope (Vec 𝕋 n) → Option (List (Zonotope (Vec 𝕋 n)))
  | 0, _ => some []
  | k + 1, R => do
    let step ← fm.relinStepAtFloat U options R (pt R)               -- (R(τ), R(t + Δt))
    let rest ← fm.relinRunAtFloat U options pt k step.2             -- the steps after it
    pure (step.1 :: rest)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
