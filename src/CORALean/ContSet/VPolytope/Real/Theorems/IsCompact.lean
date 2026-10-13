import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Order.Lattice

/-!
# A vertex description is compact

The hull of a finite set. A halfspace description is closed too but need not be
bounded, which is why the two get separate proofs rather than one.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.isCompact_construct (P : VPolytope α) : IsCompact P.construct := by
  rw [VPolytope.construct_eq_convexHull]
  exact Set.Finite.isCompact_convexHull ℝ (Set.finite_range P.V)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
