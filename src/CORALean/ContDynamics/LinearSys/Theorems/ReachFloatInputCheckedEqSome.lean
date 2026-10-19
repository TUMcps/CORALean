module

public import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInputChecked

@[expose] public section

/-!
# A checked `reachFloatInput` that returns a result returns the unchecked one

`reachFloatInputChecked` is `reachFloatInput` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachFloatInput` is
proved of the checked result, which has passed the NaN test as well.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachFloatInputChecked_eq_some (sys : LinearSys 𝕋 n)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : -- --- STMT ---
    ∀ Rs ∈ sys.reachFloatInputChecked params options,
      sys.reachFloatInput params options = some Rs ∧ noNaN (𝕋 := 𝕋) Rs = true := fun _ h =>
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
