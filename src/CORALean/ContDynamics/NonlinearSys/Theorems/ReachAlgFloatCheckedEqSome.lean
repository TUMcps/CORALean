module

public import CORALean.ContDynamics.NonlinearSys.Operations.ReachAlgFloatChecked

@[expose] public section

/-!
# A checked `reachAlgFloat` that returns a result returns the unchecked one

`reachAlgFloatChecked` is `reachAlgFloat` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachAlgFloat` is
proved of the checked result, which has passed the NaN test as well.

## Inputs
* `fm` – float Hessian model
* `alg` – abstraction algorithm
* `params` – reachability parameters
* `options` – reachability options

## Hypotheses
* none

## Conclusion
* a checked result is the unchecked result and has no NaN
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSys.FloatHessModel.reachAlgFloatChecked_eq_some
    (fm : NonlinearSys.FloatHessModel 𝕋 n m) (alg : NonlinearSys.LinReachAlg)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : -- --- CONCL ---
    ∀ Rs ∈ fm.reachAlgFloatChecked alg params options,
      fm.reachAlgFloat alg params options = some Rs ∧ noNaN (𝕋 := 𝕋) Rs = true := fun _ h =>
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
