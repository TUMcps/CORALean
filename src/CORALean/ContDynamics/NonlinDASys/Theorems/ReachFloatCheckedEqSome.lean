module

public import CORALean.ContDynamics.NonlinDASys.Operations.ReachFloatChecked

@[expose] public section

/-!
# A checked `reachFloat` that returns a result returns the unchecked one

`reachFloatChecked` is `reachFloat` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachFloat` is
proved of the checked result, which has passed the NaN test as well.

## Inputs
* `sys` – system
* `_red` – reduced ordinary model
* `fm` – float model of the reduced system
* `params` – reachability parameters with inputs
* `options` – reachability options

## Hypotheses
* none

## Conclusion
* a checked result is the unchecked one and contains no NaN
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinDASys.reachFloatChecked_eq_some {sys : NonlinDASys n p m} (_red : sys.ReducedModel)
    (fm : NonlinearSys.FloatModel 𝕋 n m)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) :
    ∀ Rs ∈ NonlinDASys.reachFloatChecked _red fm params options,
      NonlinDASys.reachFloat _red fm params options = some Rs ∧
        noNaN (𝕋 := 𝕋) Rs = true := fun _ h =>
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
