module

public import CORALean.DiscrDynamics.GridPartition.Operations.IntersectingCellsOf
public import CORALean.DiscrDynamics.GridPartition.Theorems.IntersectingCellsOuter

@[expose] public section

/-!
# `intersectingCellsOf` returns every cell that meets the set

The over-approximation for a set that is not a box, CORA's `intersectingCells(obj, zonotope)`:
the set sits in its interval hull, so a cell meeting the set meets the hull.

## Inputs
* `P` – grid partition
* `X` – set
* `c` – cell number
* `x` – point

## Hypotheses
* `hn` – dimension nonzero
* `h1` – cell number at least one
* `h2` – cell number within the cell count
* `hx` – point lies in the set
* `hxc` – point lies in the cell

## Conclusion
* the cell is returned
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every cell containing a point of `X` is among `intersectingCellsOf P X`. -/
theorem GridPartition.intersectingCellsOf_outer (P : GridPartition n) (X : S n) (hn : n ≠ 0)
    {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ P.nrOfCells) {x : Vec ℝ n} (hx : x ∈ construct X)
    (hxc : x ∈ (P.cellInterval c).construct) : c ∈ P.intersectingCellsOf X :=
  GridPartition.intersectingCells_outer P _ hn h1 h2 (Real.IntervalOuter.interval_outer X hx) hxc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
