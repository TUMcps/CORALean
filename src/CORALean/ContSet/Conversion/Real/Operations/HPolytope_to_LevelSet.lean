module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds

@[expose] public section

/-!
# A polytope as a level set — the construction

`HPolytope.levelSet` is the construction; `HPolytope_to_LevelSet` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `levelSet(P)`: `A x - b ≤ 0` stacked on `Ae x - be = 0`. -/
def HPolytope.levelSet (P : HPolytope (Vec ℝ n)) : LevelSet n where
  m := P.m + P.me
  f x := Fin.append (fun i => P.A i x - P.b i) (fun j => P.Ae j x - P.be j)
  op := Fin.append (fun _ => .le) (fun _ => .eq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
