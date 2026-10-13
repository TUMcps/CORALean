import CORALean.ContDynamics.LinearSys.Operations.ReachWrappingFreeFloatChecked

/-!
# A checked `reachWrappingFreeFloat` that returns a result returns the unchecked one

`reachWrappingFreeFloatChecked` is `reachWrappingFreeFloat` followed by `checkNoNaN`, so a
`some` of it is the unchecked `some`, and none of its floats is a NaN. Whatever is proved of
`reachWrappingFreeFloat` is proved of the checked result, which has passed the NaN test as
well.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachWrappingFreeFloatChecked_eq_some (sys : LinearSys 𝕋 n)
    (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ)
    (options : LinearSys.ReachOptions 𝕋)
    {Rs : (List (Zonotope (Vec 𝕋 n)))}
    (h : sys.reachWrappingFreeFloatChecked params options = some Rs) :
    sys.reachWrappingFreeFloat params options = some Rs ∧ noNaN (𝕋 := 𝕋) Rs = true :=
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
