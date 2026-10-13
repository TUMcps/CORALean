import CORALean.ContDynamics.NonlinDASys.Operations.ReachFloat
import CORALean.Global.Float.NoNaN

/-!
# `reachFloatChecked`, without a NaN

`reachFloat` followed by `checkNoNaN`: `none` where it is `none` or a float of its result is
a NaN. A `some` is the unchecked `some` (`reachFloatChecked_eq_some`), so whatever is proved
of `reachFloat` holds of it, and the NaN test that the trust base asks of the caller has
been made.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachFloat`, or `none` if a float of its result is a NaN. -/
def NonlinDASys.reachFloatChecked {sys : NonlinDASys n p m} (_red : sys.ReducedModel)
    (fm : NonlinearSys.FloatModel 𝕋 n m)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) :
    Option (List (Zonotope (Vec 𝕋 n))) :=
  checkNoNaN (𝕋 := 𝕋) (fm.reachFloat params options)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
