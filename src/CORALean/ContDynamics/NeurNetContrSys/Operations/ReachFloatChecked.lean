import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloat
import CORALean.Global.Float.NoNaN

/-!
# `reachFloatChecked`, without a NaN

`reachFloat` followed by `checkNoNaN`: `none` where it is `none` or a float of its result is
a NaN. A `some` is the unchecked `some` (`reachFloatChecked_eq_some`), so whatever is proved
of `reachFloat` holds of it, and the NaN test that the trust base asks of the caller has
been made.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachFloat`, or `none` if a float of its result is a NaN. -/
def NeurNetContrSys.reachFloatChecked (sys : NeurNetContrSys 𝕋 (fun k => Zonotope (Vec 𝕋 k)) n)
    (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℕ) (options : NeurNetContrSys.ReachOptions 𝕋) :
    Option (Zonotope (Vec 𝕋 n)) :=
  ifNoNaN (𝕋 := 𝕋) (sys.reachFloat params options)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
