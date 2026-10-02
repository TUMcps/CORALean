import CORALean.ContSet.LevelSet.Real.Operations.Test

/-!
# `LevelSet.contains`

CORA's `@levelSet/contains_` at a point (the numeric branch): evaluate `funHan` there and test
every component against its operator. At tolerance `0`, which is what a real point asks for;
CORA's `tol` and its set-valued branch (an interval enclosure of `funHan`) are not modelled.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `levelSet/contains_` at a point: every component passes its test. -/
noncomputable def LevelSet.contains (L : LevelSet n) (x : Vec ℝ n) : Bool :=
  (List.finRange L.m).all fun i => (L.op i).test (L.f x i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
