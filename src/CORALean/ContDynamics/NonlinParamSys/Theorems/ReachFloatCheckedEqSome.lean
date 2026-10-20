module

public import CORALean.ContDynamics.NonlinParamSys.Operations.ReachFloatChecked

@[expose] public section

/-!
# A checked `reachFloat` that returns a result returns the unchecked one

`reachFloatChecked` is `reachFloat` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachFloat` is
proved of the checked result, which has passed the NaN test as well.

## Inputs
* `_sys` – parametric system
* `fm` – float model of the augmented system
* `P` – parameter zonotope
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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.reachFloatChecked_eq_some (_sys : NonlinParamSys n m q)
    (fm : NonlinearSys.FloatModel 𝕋 (n + q) m) (P : Zonotope (Vec 𝕋 q))
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) :
    ∀ Rs ∈ NonlinParamSys.reachFloatChecked _sys fm P params options,
      NonlinParamSys.reachFloat _sys fm P params options = some Rs ∧
      noNaN (𝕋 := 𝕋) Rs = true := fun _ h =>
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
