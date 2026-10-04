import CORALean.ContSet.LevelSet.Real.LevelSet
import CORALean.ContSet.Interval.Real.Interval

/-!
# `LevelSet.isIntersecting_` at a box, one operator

CORA's `@levelSet/isIntersecting_` against a set `S` (converted to a box `I`, `type =
'approx'`): `I = ls.funHan(I)` is the interval evaluation of the function at the box, `ub =
supremum(I)`, `lb = infimum(I)`, and the verdict reads off the signs. CORALean has no interval
evaluation of a real function, so the bounds `(lb, ub)` of the evaluation are the argument `B`
(row `i`: `B i = (lb i, ub i)`), assumed a range bound (`IsRangeBound`) by the theorems. The
tolerance `tol` enters as `withinTol(·, 0, tol)`, `|·| ≤ tol`.

This is the branch `~iscell(ls.compOp)`, one operator for all rows: the per-row test of that
operator (a vector in CORA, read here as all rows).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LevelSet.isIntersecting_uniform (tol : ℝ) (op : CompOp) (B : Fin m → ℝ × ℝ) : Prop :=
  let lb : Fin m → ℝ := fun i => (B i).1
  let ub : Fin m → ℝ := fun i => (B i).2
  ∀ i,
    match op with
    | .eq => (0 < ub i ∨ |ub i| ≤ tol) ∧ (lb i < 0 ∨ |lb i| ≤ tol)
    | .le => lb i < 0 ∨ |lb i| ≤ tol
    | .lt => lb i < 0


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
