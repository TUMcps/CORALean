import CORALean.ContDynamics.NonlinParamSys.Operations.ReachFloat
import CORALean.Global.Float.NoNaN

/-!
# `reachFloatChecked`, without a NaN

`reachFloat` followed by `checkNoNaN`: `none` where it is `none` or a float of its result is
a NaN. A `some` is the unchecked `some` (`reachFloatChecked_eq_some`), so whatever is proved
of `reachFloat` holds of it, and the NaN test that the trust base asks of the caller has
been made.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachFloat`, or `none` if a float of its result is a NaN. -/
def NonlinParamSys.reachFloatChecked (_sys : NonlinParamSys n m q)
    (fm : NonlinearSys.FloatModel 𝕋 (n + q) m) (P : Zonotope 𝕋 q)
    (params : Reach.InputParams (Zonotope 𝕋 n) (Zonotope 𝕋 m) ℚ)
    (options : LinearSys.ReachOptions 𝕋) :
    Option (List (Zonotope 𝕋 n)) :=
  checkNoNaN (𝕋 := 𝕋) (NonlinParamSys.reachFloat _sys fm P params options)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
