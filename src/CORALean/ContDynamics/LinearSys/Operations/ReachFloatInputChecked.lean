import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInput
import CORALean.Global.Float.NoNaN

/-!
# `reachFloatInputChecked`: `reachFloatInput`, reported only without a NaN

`reachFloatInput` followed by `checkNoNaN`: `none` where it is `none` or a float of its
result is a NaN. A `some` is the unchecked `some` (`reachFloatInputChecked_eq_some`), so
whatever is proved of `reachFloatInput` holds of it, and the NaN test that the trust base
asks of the caller has been made.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachFloatInput`, or `none` if a float of its result is a NaN. -/
def LinearSys.reachFloatInputChecked (sys : LinearSys 𝕋 n)
    (B : Mat 𝕋 n m)
    (params : Reach.InputParams (Zonotope 𝕋 n) (Zonotope 𝕋 m) ℚ)
    (options : LinearSys.ReachOptions 𝕋) :
    Option (List (Zonotope 𝕋 n) × List (Zonotope 𝕋 n)) :=
  checkNoNaN (𝕋 := 𝕋) (sys.reachFloatInput B params options)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
