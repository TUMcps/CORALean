module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds

@[expose] public section

/-!
# A polytope as a level set

CORA's `levelSet(polytope)`: the affine function `A x - b`, every component `<= 0`. CORA throws
`notSupported` when the polytope has equality constraints; a level set carries `=` components, so
here they become `Ae x - be = 0` and the conversion is total.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


/-- `levelSet(P)`: `A x - b ≤ 0` stacked on `Ae x - be = 0`. -/
def HPolytope.levelSet (P : HPolytope (Vec ℝ n)) : LevelSet n where
  m := P.m + P.me
  f x := Fin.append (fun i => P.A i x - P.b i) (fun j => P.Ae j x - P.be j)
  op := Fin.append (fun _ => .le) (fun _ => .eq)


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.levelSet_exact (P : HPolytope (Vec ℝ n)) :
    P.levelSet.construct = P.construct := by -- --- PROOF ---
  ext x
  refine (LevelSet.forall_append_holds (fun _ => .le) (fun _ => .eq)
    (fun i => P.A i x - P.b i) (fun j => P.Ae j x - P.be j)).trans ?_
  simp only [CompOp.holds, sub_nonpos, sub_eq_zero]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
