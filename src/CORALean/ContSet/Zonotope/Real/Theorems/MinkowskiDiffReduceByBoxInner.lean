import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.IsClosed
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBySubsetAddBox
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Reduction's own box turns the reduced zonotope back into an inner approximation

The first consumer of `minkowskiDiff_inner_of_outer`: subtracting the box
`reduceBy` introduced from the zonotope it produced lands back inside the
original. `reduceBy_outer` is the other direction, so the two bracket `Z`
between two computed zonotopes.

Every hypothesis the bridge asks for is already proved of a zonotope: the box is
nonempty by `centre_mem_construct`, bounded and closed because a
zonotope is compact, and `Z` is convex.

Stated at `reduceBy` rather than at `reduceGirard` or `reduce`, which is where
`reduceBy_outer` is stated too: the ranking is a heuristic and the argument
holds at every partition. At `reduceGirard` the box would have to be `0` in the
branch where the order is already met and nothing is dropped, which says
strictly less than this does.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   08-September-2026
-- Last revision: ---


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
  minkowskiDiff_inner_of_outer ⟨_, Zonotope.centre_mem_construct _⟩
    (Zonotope.isBounded_construct _) (Zonotope.convex_construct Z)
    (Zonotope.isClosed_construct Z) (Z.reduceBy_subset_add_box part)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
