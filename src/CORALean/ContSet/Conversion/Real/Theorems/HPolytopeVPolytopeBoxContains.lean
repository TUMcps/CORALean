module

public import CORALean.ContSet.HPolytope.Real.Operations.TightAt
public import CORALean.ContSet.HPolytope.Real.Operations.BasicPoint
public import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed
public import CORALean.ContSet.HPolytope.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Positivity
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

Two routes, and they trade opposite exponentials. `vPolytope` is **exact**: a bounded polytope is
the closure of the hull of its extreme points, and at an extreme point the rows tight there admit
exactly one solution, so enumerating the subsets of rows reaches all of them. Costs `2^m`, and needs
the polytope nonempty, as CORA needs a feasible point: a subset naming nothing usable falls back on
a point inside. `vPolytopeBox` goes through a box instead, `2n` linear programs, then `2ⁿ` corners:
never tight unless the polytope was a box, but polynomial in the number of rows. Neither enumerates
facets: which subsets give vertices is a question of cost the enclosure does not depend on.

## Inputs
* `up` – certified upper bound per coordinate
* `lo` – certified lower bound per coordinate

## Hypotheses
* none

## Conclusion
* polytope is contained in its box vertex polytope
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
