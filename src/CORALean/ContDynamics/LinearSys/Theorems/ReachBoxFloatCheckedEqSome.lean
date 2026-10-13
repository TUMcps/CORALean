import CORALean.ContDynamics.LinearSys.Operations.ReachBoxFloatChecked

/-!
# A checked `reachBoxFloat` that returns a result returns the unchecked one

`reachBoxFloatChecked` is `reachBoxFloat` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachBoxFloat` is
proved of the checked result, which has passed the NaN test as well.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachBoxFloatChecked_eq_some (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec 𝕋 n))
    (r : 𝕋) (η N : ℕ) {Rs : List (Zonotope (Vec 𝕋 n))}
    (h : sys.reachBoxFloatChecked X₀ U r η N = some Rs) :
    sys.reachBoxFloat X₀ U r η N = some Rs ∧ noNaN (𝕋 := 𝕋) Rs = true :=
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
