module

public import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInput
public import CORALean.Global.Float.NoNaN

@[expose] public section

/-!
# `reachFloatInputChecked`: `reachFloatInput`, reported only without a NaN

`reachFloatInput` followed by `checkNoNaN`: `none` where it is `none` or a float of its
result is a NaN. A `some` is the unchecked `some` (`reachFloatInputChecked_eq_some`), so
whatever is proved of `reachFloatInput` holds of it, and the NaN test that the trust base
asks of the caller has been made.

## Inputs
* `sys` – linear system
* `params` – reach parameters with initial and input sets
* `options` – reach options

## Output
* windows and time-point sets of the run with inputs, or none if a result float is NaN
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachFloatInput`, or `none` if a float of its result is a NaN. -/
def LinearSys.reachFloatInputChecked (sys : LinearSys 𝕋 n)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) :
    Option (List (Zonotope (Vec 𝕋 n)) × List (Zonotope (Vec 𝕋 n))) :=
  checkNoNaN (𝕋 := 𝕋) (sys.reachFloatInput params options)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
