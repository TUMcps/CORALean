module

public import CORALean.ContSet.Polygon.Real.Polygon
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# Containment of a point in a polygon

CORA's `polygon/contains_` at a point: some piece contains it. Exact.

## Inputs
* `P` – polygon
* `x` – point of length `2`

## Hypotheses
* none

## Conclusion
* `x` lies in `P` iff it lies in some piece
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.mem_toSet_iff (P : Polygon) (x : Vec ℝ 2) :
    x ∈ ContSet.toSet P ↔ ∃ p ∈ P.sets, x ∈ VPolytope.toSet p :=
  SetUnion.mem_toSet

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
