module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.Global.Corners
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalContainsVPolytope

@[expose] public section

/-!
# A box as its corners
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `2ⁿ` corners have the box as their convex hull: `vPolytope_contains` and
`contains_vPolytope`, the latter for a nonempty box (`inf ≤ sup`), since the corners of an empty
box are not in it. -/
theorem Interval.vPolytope_exact (I : Interval (Vec ℝ n)) (hI : ∀ j, I.inf j ≤ I.sup j) :
    I.vPolytope.construct = I.construct :=
  Set.Subset.antisymm (I.contains_vPolytope hI) I.vPolytope_contains

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
