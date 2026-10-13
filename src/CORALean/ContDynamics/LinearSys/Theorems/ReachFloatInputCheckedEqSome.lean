import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInputChecked

/-!
# A checked `reachFloatInput` that returns a result returns the unchecked one

`reachFloatInputChecked` is `reachFloatInput` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachFloatInput` is
proved of the checked result, which has passed the NaN test as well.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachFloatInputChecked_eq_some (sys : LinearSys 𝕋 n)
    (B : Mat 𝕋 n m)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋)
    {Rs : (List (Zonotope (Vec 𝕋 n)) × List (Zonotope (Vec 𝕋 n)))}
    (h : sys.reachFloatInputChecked B params options = some Rs) :
    sys.reachFloatInput B params options = some Rs ∧ noNaN (𝕋 := 𝕋) Rs = true :=
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
