module

public import CORALean.ContSet.HPolytope.Real.Operations.TightAt
public import CORALean.ContSet.HPolytope.Real.Operations.BasicPoint
public import CORALean.ContSet.HPolytope.Real.Operations.BasicPointTightAt
public import CORALean.ContSet.HPolytope.Real.Theorems.ExtremePoints
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import Mathlib.Analysis.Convex.KreinMilman
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains

@[expose] public section

/-!
# Halfspaces to vertices

Two routes, and they trade opposite exponentials.

`vPolytope` is the real conversion and is **exact**. A bounded polytope is the
closure of the hull of its extreme points, and at an extreme point no direction
is free, so the rows tight there admit exactly one solution — which means every
extreme point is named by its own tight set. Enumerating the subsets of rows
therefore reaches all of them. Costs `2^m`, and needs the polytope nonempty, for
the same reason CORA needs a feasible point: a subset of rows that names nothing
usable has to fall back on something inside.

`vPolytopeBox` goes through a box instead — `2n` linear programs, then `2ⁿ`
corners. Never tight unless the polytope was a box, but polynomial in the number
of rows, which is the case that matters when a step has accumulated many.

Neither enumerates facets: nothing here identifies *which* subsets give
vertices, which is a question of cost the enclosure does not depend on.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.vPolytopeBox_contains
    (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.vPolytopeBox up lo).construct :=
  subset_trans (HPolytope.interval_contains up lo) (Interval.vPolytope_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
