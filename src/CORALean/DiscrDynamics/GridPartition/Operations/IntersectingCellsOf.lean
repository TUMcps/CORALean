module

public import CORALean.DiscrDynamics.GridPartition.Operations.IntersectingCells
public import CORALean.ContSet.Conversion.Real.Interfaces

@[expose] public section

/-!
# `GridPartition.intersectingCellsOf`

`intersectingCells` of a set that is not a box: CORA converts a zonotope or a polytope with
`interval(contSet)` and intersects that, over-approximating the set by its hull.

## Inputs
* `P` – grid partition
* `X` – set

## Output
* cell numbers that may meet the set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `intersectingCells(P, X)` of any representation `X`: the cells meeting its interval hull. -/
noncomputable def GridPartition.intersectingCellsOf (P : GridPartition n) (X : S n) : List ℕ :=
  P.intersectingCells (Real.IntervalOuter.interval X)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
