module

public import CORALean.ContDynamics.LinearSys.Operations.ReachFloatChecked

@[expose] public section

/-!
# A checked `reachFloat` that returns a result returns the unchecked one

`reachFloatChecked` is `reachFloat` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachFloat` is
proved of the checked result, which has passed the NaN test as well.

## Inputs
* `sys` – linear system
* `params` – reach parameters
* `options` – reach options

## Hypotheses
* none

## Conclusion
* a checked result equals the unchecked result and has no NaN
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachFloatChecked_eq_some (sys : LinearSys 𝕋 n)
    (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ) (options : LinearSys.ReachOptions 𝕋) :
    ∀ Rs ∈ sys.reachFloatChecked params options,
      sys.reachFloat params options = some Rs ∧ noNaN (𝕋 := 𝕋) Rs = true := fun _ h =>
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
