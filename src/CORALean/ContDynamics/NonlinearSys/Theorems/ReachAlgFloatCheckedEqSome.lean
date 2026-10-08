import CORALean.ContDynamics.NonlinearSys.Operations.ReachAlgFloatChecked

/-!
# A checked `reachAlgFloat` that returns a result returns the unchecked one

`reachAlgFloatChecked` is `reachAlgFloat` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachAlgFloat` is
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

theorem NonlinearSys.FloatHessModel.reachAlgFloatChecked_eq_some
    (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (alg : NonlinearSys.LinReachAlg)
    (params : Reach.InputParams (Zonotope 𝕋 n) (Zonotope 𝕋 m) ℚ)
    (options : LinearSys.ReachOptions 𝕋)
    {Rs : (List (Zonotope 𝕋 n))}
    (h : fm.reachAlgFloatChecked alg params options = some Rs) :
    fm.reachAlgFloat alg params options = some Rs ∧ noNaN (𝕋 := 𝕋) Rs = true :=
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
