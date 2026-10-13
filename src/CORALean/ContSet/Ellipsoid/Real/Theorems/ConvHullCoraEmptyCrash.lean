import CORALean.ContSet.Ellipsoid.Real.Operations.ConvHullCora
import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
import Mathlib.Analysis.Convex.Hull

/-!
# CORA's `ellipsoid/convHull_` errors on an empty second operand

The branch for an empty `S` (l. 56-58 of `@ellipsoid/convHull_.m`) executes `return` without
having set `S_out`, so `convHull(E, ellipsoid.empty(n))` raises MATLAB's "output argument not
assigned" error, where the hull of a convex set with `∅` is the set itself. Read from the
source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With an empty second operand CORA's `convHull_` returns no value, for any `or`, while the
hull is `E`. -/
theorem Ellipsoid.convHull_empty_cora_crash
    (orOuter : Ellipsoid n → Ellipsoid n → Ellipsoid n) (E : Ellipsoid n) :
    E.convHullCora orOuter none = none ∧
      convexHull ℝ (E.construct ∪ ∅) = E.construct := by
  refine ⟨rfl, ?_⟩
  rw [Set.union_empty]
  exact (Ellipsoid.convex_construct E).convexHull_eq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
