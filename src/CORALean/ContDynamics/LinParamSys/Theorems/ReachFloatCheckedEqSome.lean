module

public import CORALean.ContDynamics.LinParamSys.Operations.ReachFloatChecked

@[expose] public section

/-!
# A checked `reachFloat` that returns a result returns the unchecked one

`reachFloatChecked` is `reachFloat` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachFloat` is
proved of the checked result, which has passed the NaN test as well.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.reachFloatChecked_eq_some
    (sys : LinParamSys ℐ[𝕋] n)
    (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ) (options : LinearSys.ReachOptions 𝕋)
    {Rs : (List (Zonotope (Vec 𝕋 n)))}
    (h : sys.reachFloatChecked params options = some Rs) :
    sys.reachFloat params options = some Rs ∧ noNaN (𝕋 := 𝕋) Rs = true :=
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
