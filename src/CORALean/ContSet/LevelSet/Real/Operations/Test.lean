module

public import CORALean.ContSet.LevelSet.Real.LevelSet

@[expose] public section

/-!
# `CompOp.test`

The boolean test one comparison operator applies to one value: what `contains_` evaluates on
each component of `funHan`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The test one operator applies to one value. -/
noncomputable def CompOp.test (c : CompOp) (v : ℝ) : Bool :=
  match c with
  | .le => if v ≤ 0 then true else false
  | .lt => if v < 0 then true else false
  | .eq => if v = 0 then true else false

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
