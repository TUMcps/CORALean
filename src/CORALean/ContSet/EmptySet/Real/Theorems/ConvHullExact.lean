import CORALean.ContSet.EmptySet.Real.Operations.ConvHull
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# `EmptySet.convHull` is the convex hull

Exact for a convex operand, which is every `ConvexSet`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.convHull_exact {S : Type} [ContSet S (Vec ℝ n)] [ConvexSet S (Vec ℝ n)]
    (E : EmptySet n) (s : S) :
    convexHull ℝ (E.construct ∪ ContSet.construct s) = ContSet.construct (E.convHull s) := by
  change convexHull ℝ ((∅ : Set (Vec ℝ n)) ∪ ContSet.construct s) = ContSet.construct s
  rw [Set.empty_union]
  exact (ConvexSet.convex_construct s).convexHull_eq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
