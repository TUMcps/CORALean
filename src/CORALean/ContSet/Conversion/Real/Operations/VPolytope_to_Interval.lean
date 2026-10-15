module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.Interval.Real.Operations.OfCenterRadius
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# A matrix polytope as an interval matrix

CORA's `@matPolytope/intervalMatrix`: the entrywise minimum and maximum over the vertices, rebuilt
as an interval matrix from their centre `½ (min + max)` and radius `½ (max - min)`. The vertex array
of a matrix polytope with no vertex is empty in CORA; here the infimum over no vertex is `0`, and
the theorem holds vacuously, the polytope having no member.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `intMat = intervalMatrix(matP)`: the smallest box around the vertices. -/
noncomputable def VPolytope.intervalMatrix (P : VPolytope (Mat ℝ m n)) : Interval (Mat ℝ m n) :=
  -- 1. `minMat = min(V, [], 3)` and `maxMat = max(V, [], 3)`
  let minMat : Mat ℝ m n := fun i j => ⨅ l, P.V l i j
  let maxMat : Mat ℝ m n := fun i j => ⨆ l, P.V l i j
  -- 2. `C = 0.5 (minMat + maxMat)`, `D = 0.5 (maxMat - minMat)`, `intervalMatrix(C, D)`
  Interval.ofCenterRadius ((1 / 2 : ℝ) • (minMat + maxMat)) ((1 / 2 : ℝ) • (maxMat - minMat))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
