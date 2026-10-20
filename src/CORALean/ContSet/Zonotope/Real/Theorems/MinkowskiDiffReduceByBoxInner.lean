module

public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBySubsetAddBox
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# Reduction's own box turns the reduced zonotope back into an inner approximation

The first consumer of `minkowskiDiff_inner_of_outer`: subtracting the box `reduceBy` introduced
from the zonotope it produced lands back inside the original. `reduceBy_outer` is the other
direction, so the two bracket `Z` between two computed zonotopes. Every hypothesis the bridge asks
for is already proved of a zonotope: the box is nonempty by `center_mem_construct`, bounded and
closed because a zonotope is compact, and `Z` is convex. Stated at `reduceBy` rather than at
`reduceGirard` or `reduce`: the ranking is a heuristic and the argument holds at every partition.
At `reduceGirard` the box would have to be `0` where nothing is dropped, which says less.

## Inputs
* `Z` – zonotope
* `part` – split of the generator indices

## Hypotheses
* none

## Conclusion
* the reduced zonotope minus its box lies in `Z`
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   08-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An outer approximation minus its own error bound is an inner approximation,
at reduction: the reduced zonotope minus its box lies inside the original. -/
theorem Zonotope.minkowskiDiff_reduceBy_box_inner (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    minkowskiDiff (Z.reduceBy part).construct (Z.reduceByBox part).construct
      ⊆ Z.construct :=
  minkowskiDiff_inner_of_outer ⟨_, Zonotope.center_mem_construct _⟩
    (Zonotope.isBounded_construct _) (Zonotope.convex_construct Z)
    (Zonotope.isClosed_construct Z) (Z.reduceBy_subset_add_box part)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
