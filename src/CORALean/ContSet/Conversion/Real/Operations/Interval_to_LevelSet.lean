module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds

@[expose] public section

/-!
# A box as a level set — the construction

`Interval.levelSet` is the construction; `Interval_to_LevelSet` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box as `inf - x ≤ 0` stacked on `x - sup ≤ 0`. -/
def Interval.levelSet (I : Interval (Vec ℝ n)) : LevelSet n where
  m := n + n
  f x := Fin.append (fun i => I.inf i - x i) (fun i => x i - I.sup i)
  op := Fin.append (fun _ => .le) (fun _ => .le)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
