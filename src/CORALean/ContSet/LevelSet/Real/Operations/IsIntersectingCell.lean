module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `LevelSet.isIntersecting_` at a box, a cell of operators

CORA's `@levelSet/isIntersecting_` against a set `S` (converted to a box `I`, `type =
'approx'`): `I = ls.funHan(I)` is the interval evaluation of the function at the box, `ub =
supremum(I)`, `lb = infimum(I)`, and the verdict reads off the signs. CORALean has no interval
evaluation of a real function, so the bounds `(lb, ub)` of the evaluation are the argument `B`
(row `i`: `B i = (lb i, ub i)`), assumed a range bound (`IsRangeBound`) by the theorems. The
tolerance `tol` enters as `withinTol(·, 0, tol)`, `|·| ≤ tol`.

This is the branch with a cell `compOp`: each row is tested by `lb(i) < 0 | withinTol(lb(i),0,tol)`
at `<=`, and by `lb(i) < 0` at every other operator, `==` included. That is not a test of `==`,
and unsound (`Theorems/IsIntersectingCellCounterexample`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LevelSet.isIntersecting_cell (tol : ℝ) (op : Fin m → CompOp) (B : Fin m → Interval ℝ) : Prop :=
  let lb : Fin m → ℝ := fun i => (B i).inf
  let resVec : Fin m → Prop := fun i =>
    match op i with
    | .le => lb i < 0 ∨ |lb i| ≤ tol
    | _ => lb i < 0
  ∀ i, resVec i


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
