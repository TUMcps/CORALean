import CORALean.ContDynamics.LinearSys.Operations.ReachTimePointWrappingFreeFloat
import CORALean.Global.Float.NoNaN

/-!
# `reachTimePointWrappingFreeFloatChecked`, without a NaN

`reachTimePointWrappingFreeFloat` followed by `checkNoNaN`: `none` where it is `none` or a
float of its result is a NaN. A `some` is the unchecked `some`
(`reachTimePointWrappingFreeFloatChecked_eq_some`), so whatever is proved of
`reachTimePointWrappingFreeFloat` holds of it, and the NaN test that the trust base asks of
the caller has been made.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachTimePointWrappingFreeFloat`, or `none` if a float of its result is a NaN. -/
def LinearSys.reachTimePointWrappingFreeFloatChecked (sys : LinearSys 𝕋 n)
    (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) :
    Option (List (Zonotope (Vec 𝕋 n))) :=
  checkNoNaN (𝕋 := 𝕋) (sys.reachTimePointWrappingFreeFloat params options)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
